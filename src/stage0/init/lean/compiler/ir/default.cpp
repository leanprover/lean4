// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids
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
obj* l_Lean_IR_Decl_normalizeIds(obj*);
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
obj* l_Lean_IR_test___closed__6;
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
obj* _init_l_Lean_IR_test___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=== After normalize Ids ===");
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
obj* x_64; obj* x_66; obj* x_67; obj* x_69; 
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
lean::inc(x_61);
x_69 = l_IO_println___at_Lean_IR_test___spec__1(x_61, x_67);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_70 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_72 = x_69;
} else {
 lean::inc(x_70);
 lean::dec(x_69);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_7);
lean::cnstr_set(x_73, 1, x_70);
x_74 = l_Lean_IR_Decl_normalizeIds(x_61);
x_75 = l_Lean_IR_test___closed__6;
x_76 = l_IO_println___at_HasRepr_HasEval___spec__1(x_75, x_73);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; obj* x_79; obj* x_80; obj* x_81; 
x_77 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 x_79 = x_76;
} else {
 lean::inc(x_77);
 lean::dec(x_76);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_7);
lean::cnstr_set(x_80, 1, x_77);
x_81 = l_IO_println___at_Lean_IR_test___spec__1(x_74, x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 x_84 = x_81;
} else {
 lean::inc(x_82);
 lean::dec(x_81);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_7);
lean::cnstr_set(x_85, 1, x_82);
return x_85;
}
else
{
obj* x_86; obj* x_88; obj* x_90; obj* x_91; 
x_86 = lean::cnstr_get(x_81, 0);
x_88 = lean::cnstr_get(x_81, 1);
if (lean::is_exclusive(x_81)) {
 x_90 = x_81;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_81);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_86);
lean::cnstr_set(x_91, 1, x_88);
return x_91;
}
}
else
{
obj* x_93; obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_74);
x_93 = lean::cnstr_get(x_76, 0);
x_95 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 x_97 = x_76;
} else {
 lean::inc(x_93);
 lean::inc(x_95);
 lean::dec(x_76);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_93);
lean::cnstr_set(x_98, 1, x_95);
return x_98;
}
}
else
{
obj* x_100; obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_61);
x_100 = lean::cnstr_get(x_69, 0);
x_102 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 x_104 = x_69;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_69);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_100);
lean::cnstr_set(x_105, 1, x_102);
return x_105;
}
}
else
{
obj* x_107; obj* x_109; obj* x_111; obj* x_112; 
lean::dec(x_61);
x_107 = lean::cnstr_get(x_63, 0);
x_109 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 x_111 = x_63;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::dec(x_63);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set(x_112, 1, x_109);
return x_112;
}
}
else
{
obj* x_114; obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_48);
x_114 = lean::cnstr_get(x_56, 0);
x_116 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_118 = x_56;
} else {
 lean::inc(x_114);
 lean::inc(x_116);
 lean::dec(x_56);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_114);
lean::cnstr_set(x_119, 1, x_116);
return x_119;
}
}
else
{
obj* x_121; obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_48);
x_121 = lean::cnstr_get(x_50, 0);
x_123 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 x_125 = x_50;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::dec(x_50);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_121);
lean::cnstr_set(x_126, 1, x_123);
return x_126;
}
}
else
{
obj* x_128; obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_35);
x_128 = lean::cnstr_get(x_43, 0);
x_130 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_132 = x_43;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_43);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_128);
lean::cnstr_set(x_133, 1, x_130);
return x_133;
}
}
else
{
obj* x_135; obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_35);
x_135 = lean::cnstr_get(x_37, 0);
x_137 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_139 = x_37;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::dec(x_37);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_135);
lean::cnstr_set(x_140, 1, x_137);
return x_140;
}
}
else
{
obj* x_142; obj* x_144; obj* x_146; obj* x_147; 
lean::dec(x_22);
x_142 = lean::cnstr_get(x_30, 0);
x_144 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_146 = x_30;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::dec(x_30);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_142);
lean::cnstr_set(x_147, 1, x_144);
return x_147;
}
}
else
{
obj* x_149; obj* x_151; obj* x_153; obj* x_154; 
lean::dec(x_22);
x_149 = lean::cnstr_get(x_24, 0);
x_151 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_153 = x_24;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::dec(x_24);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_149);
lean::cnstr_set(x_154, 1, x_151);
return x_154;
}
}
else
{
obj* x_156; obj* x_158; obj* x_160; obj* x_161; 
lean::dec(x_0);
x_156 = lean::cnstr_get(x_16, 0);
x_158 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_160 = x_16;
} else {
 lean::inc(x_156);
 lean::inc(x_158);
 lean::dec(x_16);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_156);
lean::cnstr_set(x_161, 1, x_158);
return x_161;
}
}
else
{
obj* x_163; obj* x_165; obj* x_167; obj* x_168; 
lean::dec(x_0);
x_163 = lean::cnstr_get(x_3, 0);
x_165 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_167 = x_3;
} else {
 lean::inc(x_163);
 lean::inc(x_165);
 lean::dec(x_3);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_163);
lean::cnstr_set(x_168, 1, x_165);
return x_168;
}
}
}
}}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
obj* initialize_init_lean_compiler_ir_pushproj(obj*);
obj* initialize_init_lean_compiler_ir_elimdead(obj*);
obj* initialize_init_lean_compiler_ir_simpcase(obj*);
obj* initialize_init_lean_compiler_ir_resetreuse(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_pushproj(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_resetreuse(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
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
 l_Lean_IR_test___closed__6 = _init_l_Lean_IR_test___closed__6();
lean::mark_persistent(l_Lean_IR_test___closed__6);
return w;
}
