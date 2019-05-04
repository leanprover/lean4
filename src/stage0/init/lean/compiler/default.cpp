// Lean compiler output
// Module: init.lean.compiler.default
// Imports: init.lean.compiler.constfolding init.lean.compiler.ir init.lean.compiler.pushproj init.lean.compiler.elimdead init.lean.compiler.simpcase init.lean.compiler.resetreuse
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
obj* l_Lean_IR_test___closed__5;
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
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
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
x_0 = lean::mk_string("=== After insert reset reuse ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After elim dead locals ===");
return x_0;
}
}
obj* _init_l_Lean_IR_test___closed__5() {
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
x_35 = l_Lean_IR_Decl_insertResetReuse___main(x_22);
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
x_48 = l_Lean_IR_Decl_elimDead___main(x_35);
x_49 = l_Lean_IR_test___closed__4;
x_50 = l_IO_println___at_HasRepr_HasEval___spec__1(x_49, x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_56; 
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
lean::inc(x_48);
x_56 = l_IO_println___at_Lean_IR_test___spec__1(x_48, x_54);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_57 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_59 = x_56;
} else {
 lean::inc(x_57);
 lean::dec(x_56);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_7);
lean::cnstr_set(x_60, 1, x_57);
x_61 = l_Lean_IR_Decl_simpCase___main(x_48);
x_62 = l_Lean_IR_test___closed__5;
x_63 = l_IO_println___at_HasRepr_HasEval___spec__1(x_62, x_60);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_64 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_66 = x_63;
} else {
 lean::inc(x_64);
 lean::dec(x_63);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_7);
lean::cnstr_set(x_67, 1, x_64);
x_68 = l_IO_println___at_Lean_IR_test___spec__1(x_61, x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_72; 
x_69 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_71 = x_68;
} else {
 lean::inc(x_69);
 lean::dec(x_68);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_7);
lean::cnstr_set(x_72, 1, x_69);
return x_72;
}
else
{
obj* x_73; obj* x_75; obj* x_77; obj* x_78; 
x_73 = lean::cnstr_get(x_68, 0);
x_75 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_77 = x_68;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_68);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_73);
lean::cnstr_set(x_78, 1, x_75);
return x_78;
}
}
else
{
obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_61);
x_80 = lean::cnstr_get(x_63, 0);
x_82 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 x_84 = x_63;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_63);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_80);
lean::cnstr_set(x_85, 1, x_82);
return x_85;
}
}
else
{
obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_48);
x_87 = lean::cnstr_get(x_56, 0);
x_89 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_91 = x_56;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_56);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_87);
lean::cnstr_set(x_92, 1, x_89);
return x_92;
}
}
else
{
obj* x_94; obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_48);
x_94 = lean::cnstr_get(x_50, 0);
x_96 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_98 = x_50;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_50);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_94);
lean::cnstr_set(x_99, 1, x_96);
return x_99;
}
}
else
{
obj* x_101; obj* x_103; obj* x_105; obj* x_106; 
lean::dec(x_35);
x_101 = lean::cnstr_get(x_43, 0);
x_103 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_105 = x_43;
} else {
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_43);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_101);
lean::cnstr_set(x_106, 1, x_103);
return x_106;
}
}
else
{
obj* x_108; obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_35);
x_108 = lean::cnstr_get(x_37, 0);
x_110 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_112 = x_37;
} else {
 lean::inc(x_108);
 lean::inc(x_110);
 lean::dec(x_37);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_108);
lean::cnstr_set(x_113, 1, x_110);
return x_113;
}
}
else
{
obj* x_115; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_22);
x_115 = lean::cnstr_get(x_30, 0);
x_117 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_119 = x_30;
} else {
 lean::inc(x_115);
 lean::inc(x_117);
 lean::dec(x_30);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_115);
lean::cnstr_set(x_120, 1, x_117);
return x_120;
}
}
else
{
obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_22);
x_122 = lean::cnstr_get(x_24, 0);
x_124 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_126 = x_24;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_24);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_122);
lean::cnstr_set(x_127, 1, x_124);
return x_127;
}
}
else
{
obj* x_129; obj* x_131; obj* x_133; obj* x_134; 
lean::dec(x_0);
x_129 = lean::cnstr_get(x_16, 0);
x_131 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_133 = x_16;
} else {
 lean::inc(x_129);
 lean::inc(x_131);
 lean::dec(x_16);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_129);
lean::cnstr_set(x_134, 1, x_131);
return x_134;
}
}
else
{
obj* x_136; obj* x_138; obj* x_140; obj* x_141; 
lean::dec(x_0);
x_136 = lean::cnstr_get(x_3, 0);
x_138 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_140 = x_3;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_3);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_136);
lean::cnstr_set(x_141, 1, x_138);
return x_141;
}
}
}
}}
obj* initialize_init_lean_compiler_constfolding(obj*);
obj* initialize_init_lean_compiler_ir(obj*);
obj* initialize_init_lean_compiler_pushproj(obj*);
obj* initialize_init_lean_compiler_elimdead(obj*);
obj* initialize_init_lean_compiler_simpcase(obj*);
obj* initialize_init_lean_compiler_resetreuse(obj*);
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
w = initialize_init_lean_compiler_resetreuse(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_test___closed__1 = _init_l_Lean_IR_test___closed__1();
lean::mark_persistent(l_Lean_IR_test___closed__1);
 l_Lean_IR_test___closed__2 = _init_l_Lean_IR_test___closed__2();
lean::mark_persistent(l_Lean_IR_test___closed__2);
 l_Lean_IR_test___closed__3 = _init_l_Lean_IR_test___closed__3();
lean::mark_persistent(l_Lean_IR_test___closed__3);
 l_Lean_IR_test___closed__4 = _init_l_Lean_IR_test___closed__4();
lean::mark_persistent(l_Lean_IR_test___closed__4);
 l_Lean_IR_test___closed__5 = _init_l_Lean_IR_test___closed__5();
lean::mark_persistent(l_Lean_IR_test___closed__5);
return w;
}
