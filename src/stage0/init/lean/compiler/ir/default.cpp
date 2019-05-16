// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.boxing
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
obj* l_Lean_IR_test(obj*, obj*);
namespace lean {
namespace ir {
obj* decl_to_string_core(obj*);
}}
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_IO_println___at_Lean_IR_test___spec__1(obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl___main(obj*, obj*);
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_compileAux(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_IR_test___closed__1;
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Lean_IR_test___closed__4;
obj* l_Lean_IR_compileAux___boxed(obj*, obj*);
obj* l_IO_println___at_HasRepr_HasEval___spec__1(obj*, obj*);
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
obj* l_Lean_IR_test___closed__6;
obj* l_Lean_IR_compileAux___rarg(obj*);
obj* l_IO_print___at_Lean_IR_test___spec__2(obj*, obj*);
obj* l_Lean_IR_Decl_simpCase___main(obj*);
extern obj* l_IO_println___rarg___closed__1;
obj* l_Lean_IR_Decl_check(obj*, obj*);
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
x_0 = lean::mk_string("Max index ");
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
obj* l_Lean_IR_test(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = l_Lean_IR_Decl_check(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
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
lean::inc(x_0);
x_10 = l_IO_println___at_Lean_IR_test___spec__1(x_0, x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_11 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_13 = x_10;
} else {
 lean::inc(x_11);
 lean::dec(x_10);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_11);
x_15 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_17 = l_Lean_IR_MaxIndex_collectDecl___main(x_0, x_15);
x_18 = l_Nat_repr(x_17);
x_19 = l_Lean_IR_test___closed__1;
x_20 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_22 = l_IO_println___at_HasRepr_HasEval___spec__1(x_20, x_14);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_24);
x_28 = l_Lean_IR_Decl_pushProj___main(x_0);
x_29 = l_Lean_IR_test___closed__2;
x_30 = l_IO_println___at_HasRepr_HasEval___spec__1(x_29, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
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
lean::inc(x_28);
x_36 = l_IO_println___at_Lean_IR_test___spec__1(x_28, x_34);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_39 = x_36;
} else {
 lean::inc(x_37);
 lean::dec(x_36);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_7);
lean::cnstr_set(x_40, 1, x_37);
x_41 = l_Lean_IR_Decl_insertResetReuse___main(x_28);
x_42 = l_Lean_IR_test___closed__3;
x_43 = l_IO_println___at_HasRepr_HasEval___spec__1(x_42, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; 
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
lean::inc(x_41);
x_49 = l_IO_println___at_Lean_IR_test___spec__1(x_41, x_47);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_50 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 x_52 = x_49;
} else {
 lean::inc(x_50);
 lean::dec(x_49);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_7);
lean::cnstr_set(x_53, 1, x_50);
x_54 = l_Lean_IR_Decl_elimDead___main(x_41);
x_55 = l_Lean_IR_test___closed__4;
x_56 = l_IO_println___at_HasRepr_HasEval___spec__1(x_55, x_53);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; 
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
lean::inc(x_54);
x_62 = l_IO_println___at_Lean_IR_test___spec__1(x_54, x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_65 = x_62;
} else {
 lean::inc(x_63);
 lean::dec(x_62);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_7);
lean::cnstr_set(x_66, 1, x_63);
x_67 = l_Lean_IR_Decl_simpCase___main(x_54);
x_68 = l_Lean_IR_test___closed__5;
x_69 = l_IO_println___at_HasRepr_HasEval___spec__1(x_68, x_66);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_73; obj* x_75; 
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
lean::inc(x_67);
x_75 = l_IO_println___at_Lean_IR_test___spec__1(x_67, x_73);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_76 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_78 = x_75;
} else {
 lean::inc(x_76);
 lean::dec(x_75);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_7);
lean::cnstr_set(x_79, 1, x_76);
x_80 = l_Lean_IR_Decl_normalizeIds(x_67);
x_81 = l_Lean_IR_test___closed__6;
x_82 = l_IO_println___at_HasRepr_HasEval___spec__1(x_81, x_79);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; 
x_83 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 x_85 = x_82;
} else {
 lean::inc(x_83);
 lean::dec(x_82);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_83);
lean::inc(x_80);
x_88 = l_IO_println___at_Lean_IR_test___spec__1(x_80, x_86);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_91 = x_88;
} else {
 lean::inc(x_89);
 lean::dec(x_88);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_7);
lean::cnstr_set(x_92, 1, x_89);
x_93 = l_Lean_IR_Decl_check(x_80, x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_96; obj* x_97; 
x_94 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 x_96 = x_93;
} else {
 lean::inc(x_94);
 lean::dec(x_93);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_7);
lean::cnstr_set(x_97, 1, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_100; obj* x_102; obj* x_103; 
x_98 = lean::cnstr_get(x_93, 0);
x_100 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_102 = x_93;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_93);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_98);
lean::cnstr_set(x_103, 1, x_100);
return x_103;
}
}
else
{
obj* x_105; obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_80);
x_105 = lean::cnstr_get(x_88, 0);
x_107 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 x_109 = x_88;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_88);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_105);
lean::cnstr_set(x_110, 1, x_107);
return x_110;
}
}
else
{
obj* x_112; obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_80);
x_112 = lean::cnstr_get(x_82, 0);
x_114 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 x_116 = x_82;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_82);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_112);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
else
{
obj* x_119; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_67);
x_119 = lean::cnstr_get(x_75, 0);
x_121 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_123 = x_75;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_75);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_119);
lean::cnstr_set(x_124, 1, x_121);
return x_124;
}
}
else
{
obj* x_126; obj* x_128; obj* x_130; obj* x_131; 
lean::dec(x_67);
x_126 = lean::cnstr_get(x_69, 0);
x_128 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 x_130 = x_69;
} else {
 lean::inc(x_126);
 lean::inc(x_128);
 lean::dec(x_69);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_126);
lean::cnstr_set(x_131, 1, x_128);
return x_131;
}
}
else
{
obj* x_133; obj* x_135; obj* x_137; obj* x_138; 
lean::dec(x_54);
x_133 = lean::cnstr_get(x_62, 0);
x_135 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 x_137 = x_62;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_62);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_133);
lean::cnstr_set(x_138, 1, x_135);
return x_138;
}
}
else
{
obj* x_140; obj* x_142; obj* x_144; obj* x_145; 
lean::dec(x_54);
x_140 = lean::cnstr_get(x_56, 0);
x_142 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_144 = x_56;
} else {
 lean::inc(x_140);
 lean::inc(x_142);
 lean::dec(x_56);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_140);
lean::cnstr_set(x_145, 1, x_142);
return x_145;
}
}
else
{
obj* x_147; obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_41);
x_147 = lean::cnstr_get(x_49, 0);
x_149 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 x_151 = x_49;
} else {
 lean::inc(x_147);
 lean::inc(x_149);
 lean::dec(x_49);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_147);
lean::cnstr_set(x_152, 1, x_149);
return x_152;
}
}
else
{
obj* x_154; obj* x_156; obj* x_158; obj* x_159; 
lean::dec(x_41);
x_154 = lean::cnstr_get(x_43, 0);
x_156 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 x_158 = x_43;
} else {
 lean::inc(x_154);
 lean::inc(x_156);
 lean::dec(x_43);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_154);
lean::cnstr_set(x_159, 1, x_156);
return x_159;
}
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; 
lean::dec(x_28);
x_161 = lean::cnstr_get(x_36, 0);
x_163 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 x_165 = x_36;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_36);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_161);
lean::cnstr_set(x_166, 1, x_163);
return x_166;
}
}
else
{
obj* x_168; obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_28);
x_168 = lean::cnstr_get(x_30, 0);
x_170 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_172 = x_30;
} else {
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_30);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_168);
lean::cnstr_set(x_173, 1, x_170);
return x_173;
}
}
else
{
obj* x_175; obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_0);
x_175 = lean::cnstr_get(x_22, 0);
x_177 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_179 = x_22;
} else {
 lean::inc(x_175);
 lean::inc(x_177);
 lean::dec(x_22);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_175);
lean::cnstr_set(x_180, 1, x_177);
return x_180;
}
}
else
{
obj* x_182; obj* x_184; obj* x_186; obj* x_187; 
lean::dec(x_0);
x_182 = lean::cnstr_get(x_10, 0);
x_184 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_186 = x_10;
} else {
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_10);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_182);
lean::cnstr_set(x_187, 1, x_184);
return x_187;
}
}
else
{
obj* x_189; obj* x_191; obj* x_193; obj* x_194; 
lean::dec(x_0);
x_189 = lean::cnstr_get(x_3, 0);
x_191 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_193 = x_3;
} else {
 lean::inc(x_189);
 lean::inc(x_191);
 lean::dec(x_3);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_189);
lean::cnstr_set(x_194, 1, x_191);
return x_194;
}
}
}
obj* l_Lean_IR_compileAux___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = lean::box(0);
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_IR_compileAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_compileAux___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_IR_compileAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_compileAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_pushproj(obj*);
obj* initialize_init_lean_compiler_ir_elimdead(obj*);
obj* initialize_init_lean_compiler_ir_simpcase(obj*);
obj* initialize_init_lean_compiler_ir_resetreuse(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
obj* initialize_init_lean_compiler_ir_checker(obj*);
obj* initialize_init_lean_compiler_ir_boxing(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
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
w = initialize_init_lean_compiler_ir_checker(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
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
