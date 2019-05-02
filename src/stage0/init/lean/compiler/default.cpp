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
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_MaxVar_collectDecl___main(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_IR_test___closed__1;
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Lean_IR_test___closed__4;
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
x_0 = lean::mk_string("Max variable ");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After push projections ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After elim dead locals ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__4() {
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
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_9 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_11 = l_Lean_IR_MaxVar_collectDecl___main(x_0, x_9);
x_12 = l_Nat_repr(x_11);
x_13 = l_Lean_IR_test___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = l_IO_println___at_HasRepr_HasEval___spec__1(x_14, x_8);
lean::dec(x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_20 = x_16;
} else {
 lean::inc(x_18);
 lean::dec(x_16);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_7);
lean::cnstr_set(x_21, 1, x_18);
x_22 = l_Lean_IR_Decl_pushProj___main(x_0);
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
x_35 = l_Lean_IR_Decl_elimDead___main(x_22);
x_36 = l_Lean_IR_test___closed__3;
x_37 = l_IO_println___at_HasRepr_HasEval___spec__1(x_36, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; 
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
lean::inc(x_35);
x_43 = l_IO_println___at_Lean_IR_test___spec__1(x_35, x_41);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_44 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_46 = x_43;
} else {
 lean::inc(x_44);
 lean::dec(x_43);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_7);
lean::cnstr_set(x_47, 1, x_44);
x_48 = l_Lean_IR_Decl_simpCase___main(x_35);
x_49 = l_Lean_IR_test___closed__4;
x_50 = l_IO_println___at_HasRepr_HasEval___spec__1(x_49, x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_53 = x_50;
} else {
 lean::inc(x_51);
 lean::dec(x_50);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_7);
lean::cnstr_set(x_54, 1, x_51);
x_55 = l_IO_println___at_Lean_IR_test___spec__1(x_48, x_54);
return x_55;
}
else
{
obj* x_57; obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_48);
x_57 = lean::cnstr_get(x_50, 0);
x_59 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_61 = x_50;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_50);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_57);
lean::cnstr_set(x_62, 1, x_59);
return x_62;
}
}
else
{
obj* x_64; obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_35);
x_64 = lean::cnstr_get(x_43, 0);
x_66 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_68 = x_43;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_43);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_66);
return x_69;
}
}
else
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_35);
x_71 = lean::cnstr_get(x_37, 0);
x_73 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_75 = x_37;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_37);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_71);
lean::cnstr_set(x_76, 1, x_73);
return x_76;
}
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_22);
x_78 = lean::cnstr_get(x_30, 0);
x_80 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_82 = x_30;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_30);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_78);
lean::cnstr_set(x_83, 1, x_80);
return x_83;
}
}
else
{
obj* x_85; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_22);
x_85 = lean::cnstr_get(x_24, 0);
x_87 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_89 = x_24;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_24);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_85);
lean::cnstr_set(x_90, 1, x_87);
return x_90;
}
}
else
{
obj* x_92; obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_0);
x_92 = lean::cnstr_get(x_16, 0);
x_94 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_96 = x_16;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_16);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_92);
lean::cnstr_set(x_97, 1, x_94);
return x_97;
}
}
else
{
obj* x_99; obj* x_101; obj* x_103; obj* x_104; 
lean::dec(x_0);
x_99 = lean::cnstr_get(x_3, 0);
x_101 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_103 = x_3;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_3);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_99);
lean::cnstr_set(x_104, 1, x_101);
return x_104;
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
 l_Lean_IR_test___closed__4 = _init_l_Lean_IR_test___closed__4();
lean::mark_persistent(l_Lean_IR_test___closed__4);
return w;
}
