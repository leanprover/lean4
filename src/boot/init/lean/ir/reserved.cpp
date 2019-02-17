// Lean compiler output
// Module: init.lean.ir.reserved
// Imports: init.data.rbtree.basic init.lean.name
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
obj* l_lean_ir_reserved__set;
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_is__reserved___spec__1(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_ir_reserved__set___spec__5(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_reserved__set___spec__2(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_reserved__set___spec__3(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_lean_ir_is__reserved___spec__3(obj*, obj*);
uint8 l_lean_ir_is__reserved(obj*);
obj* l_lean_ir_is__reserved__name___boxed(obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
uint8 l_option_is__some___main___rarg(obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
uint8 l_lean_ir_is__reserved__name(obj*);
obj* l_rbtree_insert___at_lean_ir_reserved__set___spec__1(obj*, obj*);
obj* l_lean_ir_reserved;
obj* l_lean_ir_is__reserved__name___main___boxed(obj*);
uint8 l_lean_ir_is__reserved__name___main(obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_ir_is__reserved___boxed(obj*);
obj* l_rbmap_find__core___main___at_lean_ir_is__reserved___spec__2(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* _init_l_lean_ir_reserved() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_0 = lean::box(0);
x_1 = lean::mk_string("external");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::mk_string("def");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_string("jmp");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::mk_string("case");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::mk_string("ret");
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::mk_string("phi");
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::mk_string("array_write");
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::mk_string("sarray");
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::mk_string("array");
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::mk_string("apply");
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::mk_string("closure");
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = lean::mk_string("sget");
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::mk_string("sset");
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = lean::mk_string("get");
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::mk_string("set");
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::mk_string("cnstr");
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
x_33 = lean::mk_string("call");
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
x_35 = lean::mk_string("sarray_pop");
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::mk_string("array_pop");
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
x_39 = lean::mk_string("dealloc");
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = lean::mk_string("free");
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = lean::mk_string("dec");
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::mk_string("inc");
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = lean::mk_string("dec_sref");
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
x_49 = lean::mk_string("dec_ref");
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_48);
x_51 = lean::mk_string("inc_ref");
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
x_53 = lean::mk_string("string_append");
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::mk_string("string_push");
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_54);
x_57 = lean::mk_string("array_push");
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_56);
x_59 = lean::mk_string("array_read");
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_58);
x_61 = lean::mk_string("ine");
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_60);
x_63 = lean::mk_string("ieq");
x_64 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean::mk_string("ilt");
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
x_67 = lean::mk_string("ile");
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
x_69 = lean::mk_string("ne");
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::mk_string("eq");
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::mk_string("lt");
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_72);
x_75 = lean::mk_string("le");
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::mk_string("xor");
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::mk_string("or");
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = lean::mk_string("and");
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::mk_string("shr");
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
x_85 = lean::mk_string("shl");
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_84);
x_87 = lean::mk_string("imod");
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_86);
x_89 = lean::mk_string("idiv");
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::mk_string("imul");
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
x_93 = lean::mk_string("isub");
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_92);
x_95 = lean::mk_string("iadd");
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::mk_string("mod");
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_96);
x_99 = lean::mk_string("div");
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_98);
x_101 = lean::mk_string("mul");
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_100);
x_103 = lean::mk_string("sub");
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_102);
x_105 = lean::mk_string("add");
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_104);
x_107 = lean::mk_string("tag_ref");
x_108 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_106);
x_109 = lean::mk_string("tag");
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_108);
x_111 = lean::mk_string("succ");
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_110);
x_113 = lean::mk_string("string_len");
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_112);
x_115 = lean::mk_string("sarray_size");
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_114);
x_117 = lean::mk_string("array_size");
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_116);
x_119 = lean::mk_string("sarray_copy");
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_118);
x_121 = lean::mk_string("array_copy");
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_120);
x_123 = lean::mk_string("cast");
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_122);
x_125 = lean::mk_string("box");
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_124);
x_127 = lean::mk_string("unbox");
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_126);
x_129 = lean::mk_string("is_null");
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_128);
x_131 = lean::mk_string("is_shared");
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_130);
x_133 = lean::mk_string("is_scalar");
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_132);
x_135 = lean::mk_string("nat2int");
x_136 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean::mk_string("ineg");
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_136);
x_139 = lean::mk_string("neg");
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_138);
x_141 = lean::mk_string("not");
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_140);
x_143 = lean::mk_string("object");
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_142);
x_145 = lean::mk_string("double");
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::mk_string("float");
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_146);
x_149 = lean::mk_string("int64");
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_148);
x_151 = lean::mk_string("int32");
x_152 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_150);
x_153 = lean::mk_string("int16");
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_152);
x_155 = lean::mk_string("usize");
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_155);
lean::cnstr_set(x_156, 1, x_154);
x_157 = lean::mk_string("uint64");
x_158 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_156);
x_159 = lean::mk_string("uint32");
x_160 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_158);
x_161 = lean::mk_string("uint16");
x_162 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_160);
x_163 = lean::mk_string("byte");
x_164 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_162);
x_165 = lean::mk_string("bool");
x_166 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_164);
return x_166;
}
}
obj* l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; uint8 x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::string_dec_lt(x_1, x_6);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean::string_dec_lt(x_6, x_1);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_2);
lean::cnstr_set(x_17, 3, x_10);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_19 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_19 = x_12;
}
lean::cnstr_set(x_19, 0, x_4);
lean::cnstr_set(x_19, 1, x_6);
lean::cnstr_set(x_19, 2, x_8);
lean::cnstr_set(x_19, 3, x_18);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_21 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_21 = x_12;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
lean::cnstr_set(x_21, 2, x_8);
lean::cnstr_set(x_21, 3, x_10);
return x_21;
}
}
default:
{
obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; uint8 x_31; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 2);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 3);
lean::inc(x_28);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_30 = x_0;
} else {
 lean::dec(x_0);
 x_30 = lean::box(0);
}
x_31 = lean::string_dec_lt(x_1, x_24);
if (x_31 == 0)
{
uint8 x_32; 
x_32 = lean::string_dec_lt(x_24, x_1);
if (x_32 == 0)
{
obj* x_35; 
lean::dec(x_24);
lean::dec(x_26);
if (lean::is_scalar(x_30)) {
 x_35 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_35 = x_30;
}
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_1);
lean::cnstr_set(x_35, 2, x_2);
lean::cnstr_set(x_35, 3, x_28);
return x_35;
}
else
{
uint8 x_37; 
lean::inc(x_28);
x_37 = l_rbnode_get__color___main___rarg(x_28);
if (x_37 == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_30);
x_39 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_28, x_1, x_2);
x_40 = l_rbnode_balance2__node___main___rarg(x_39, x_24, x_26, x_22);
return x_40;
}
else
{
obj* x_41; obj* x_42; 
x_41 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_28, x_1, x_2);
if (lean::is_scalar(x_30)) {
 x_42 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_42 = x_30;
}
lean::cnstr_set(x_42, 0, x_22);
lean::cnstr_set(x_42, 1, x_24);
lean::cnstr_set(x_42, 2, x_26);
lean::cnstr_set(x_42, 3, x_41);
return x_42;
}
}
}
else
{
uint8 x_44; 
lean::inc(x_22);
x_44 = l_rbnode_get__color___main___rarg(x_22);
if (x_44 == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_30);
x_46 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_22, x_1, x_2);
x_47 = l_rbnode_balance1__node___main___rarg(x_46, x_24, x_26, x_28);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_22, x_1, x_2);
if (lean::is_scalar(x_30)) {
 x_49 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_49 = x_30;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_24);
lean::cnstr_set(x_49, 2, x_26);
lean::cnstr_set(x_49, 3, x_28);
return x_49;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_reserved__set___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_reserved__set___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_reserved__set___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_reserved__set___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbtree_insert___at_lean_ir_reserved__set___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_rbnode_insert___at_lean_ir_reserved__set___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_ir_reserved__set___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_rbnode_insert___at_lean_ir_reserved__set___spec__3(x_0, x_2, x_7);
x_0 = x_8;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_lean_ir_reserved__set() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_ir_reserved;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_ir_reserved__set___spec__5(x_0, x_1);
return x_3;
}
}
obj* l_rbnode_find__core___main___at_lean_ir_is__reserved___spec__3(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::string_dec_lt(x_1, x_6);
if (x_13 == 0)
{
uint8 x_15; 
lean::dec(x_4);
x_15 = lean::string_dec_lt(x_6, x_1);
if (x_15 == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_8);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint8 x_36; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 2);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 3);
lean::inc(x_33);
lean::dec(x_0);
x_36 = lean::string_dec_lt(x_1, x_29);
if (x_36 == 0)
{
uint8 x_38; 
lean::dec(x_27);
x_38 = lean::string_dec_lt(x_29, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_1);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_29);
lean::cnstr_set(x_41, 1, x_31);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
else
{
lean::dec(x_29);
lean::dec(x_31);
x_0 = x_33;
goto _start;
}
}
else
{
lean::dec(x_29);
lean::dec(x_33);
lean::dec(x_31);
x_0 = x_27;
goto _start;
}
}
}
}
}
obj* l_rbmap_find__core___main___at_lean_ir_is__reserved___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_is__reserved___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_is__reserved___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_is__reserved___spec__3(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
}
}
uint8 l_lean_ir_is__reserved(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; uint8 x_4; 
x_1 = l_lean_ir_reserved__set;
lean::inc(x_1);
x_3 = l_rbtree_find___at_lean_ir_is__reserved___spec__1(x_1, x_0);
x_4 = l_option_is__some___main___rarg(x_3);
return x_4;
}
}
obj* l_lean_ir_is__reserved___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_is__reserved(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_lean_ir_is__reserved__name___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 1:
{
obj* x_2; uint8 x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_ir_is__reserved(x_2);
return x_5;
}
default:
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
}
}
}
obj* l_lean_ir_is__reserved__name___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_is__reserved__name___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_lean_ir_is__reserved__name(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_is__reserved__name___main(x_0);
return x_1;
}
}
obj* l_lean_ir_is__reserved__name___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_is__reserved__name(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
void initialize_init_data_rbtree_basic();
void initialize_init_lean_name();
static bool _G_initialized = false;
void initialize_init_lean_ir_reserved() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_rbtree_basic();
 initialize_init_lean_name();
 l_lean_ir_reserved = _init_l_lean_ir_reserved();
 l_lean_ir_reserved__set = _init_l_lean_ir_reserved__set();
}
