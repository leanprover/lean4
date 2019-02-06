// Lean compiler output
// Module: init.lean.ir.lirc
// Imports: init.lean.ir.parser init.lean.ir.type_check init.lean.ir.ssa_check init.lean.ir.extract_cpp init.lean.ir.format init.lean.ir.elim_phi
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l___private_2142412293__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_lirc___boxed(obj*, obj*, obj*);
unsigned char l_char_is__whitespace(unsigned);
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
obj* l_lean_ir_elim__phi(obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_ir_check(obj*, unsigned char, obj*);
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l___private_2038417741__mk__consumed__result___rarg(unsigned char, obj*);
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_ir_parse__decl(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(unsigned, obj*);
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4(obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_symbol(obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(obj*, unsigned char, obj*);
obj* l_option_orelse___main___rarg(obj*, obj*);
unsigned char l_char_is__alpha(unsigned);
obj* l_lean_ir_parse__input___lambda__1(obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
extern obj* l_lean_ir_mk__fnid2string;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_ir_lirc(obj*, obj*, unsigned char);
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_extract__cpp(obj*, obj*);
obj* l_lean_parser_parsec_message_to__string___rarg(obj*);
obj* l_lean_ir_check__blockids(obj*);
extern obj* l_list_repr___main___rarg___closed__3;
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_ir_parse__input__aux(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_update__env(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l___private_31565857__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_ir_lirc___spec__2(obj*);
extern obj* l_lean_ir_var_declare___closed__1;
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(obj*);
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_lean_ir_parse__input(obj*);
obj* l_lean_ir_decl_valid__ssa(obj*);
obj* l_lean_ir_parse__input__aux___main(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(obj*, obj*);
obj* l_lean_ir_decl_name(obj*);
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(obj*, obj*);
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_ir_check___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(obj*);
unsigned char l_char_is__alphanum(unsigned);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5___boxed(obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj*);
obj* l_lean_ir_type__check(obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(obj*, unsigned char, obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_update__external__names(obj*, obj*, obj*);
obj* l_char_quote__core(unsigned);
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_parse__input__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_15; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_0, x_7);
lean::dec(x_7);
lean::dec(x_0);
x_11 = lean::box(0);
lean::inc(x_3);
x_15 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 2);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_20 = x_15;
}
lean::inc(x_1);
x_22 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_2);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_16);
lean::cnstr_set(x_27, 2, x_25);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_12 = x_28;
goto lbl_13;
}
else
{
obj* x_29; unsigned char x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<unsigned char>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_32 = x_15;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
x_12 = x_34;
goto lbl_13;
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_12;
}
else
{
obj* x_40; unsigned char x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; 
x_40 = lean::cnstr_get(x_12, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (x_42 == 0)
{
obj* x_50; obj* x_53; 
lean::dec(x_12);
x_50 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_50);
x_53 = l_lean_ir_symbol(x_50, x_3);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 2);
lean::inc(x_56);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 lean::cnstr_release(x_53, 2);
 x_58 = x_53;
}
x_59 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_54);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_67; 
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_59, 2);
lean::inc(x_64);
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 lean::cnstr_release(x_59, 2);
 x_66 = x_59;
}
x_67 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_62);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
if (lean::is_scalar(x_58)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_58;
}
lean::cnstr_set(x_75, 0, x_60);
lean::cnstr_set(x_75, 1, x_68);
lean::cnstr_set(x_75, 2, x_73);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_85; obj* x_87; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = l_list_repr___main___rarg___closed__3;
lean::inc(x_85);
x_87 = l_lean_ir_symbol(x_85, x_80);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_90; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_88 = lean::cnstr_get(x_87, 1);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 2);
lean::inc(x_90);
lean::dec(x_87);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_78);
lean::inc(x_73);
if (lean::is_scalar(x_66)) {
 x_95 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_95 = x_66;
}
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_88);
lean::cnstr_set(x_95, 2, x_73);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_95);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_96);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_97);
x_47 = x_98;
goto lbl_48;
}
else
{
obj* x_101; unsigned char x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_78);
lean::dec(x_66);
x_101 = lean::cnstr_get(x_87, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<unsigned char>(x_87, sizeof(void*)*1);
if (lean::is_shared(x_87)) {
 lean::dec(x_87);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_87, 0);
 x_104 = x_87;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_107);
x_47 = x_108;
goto lbl_48;
}
}
else
{
obj* x_110; unsigned char x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_66);
x_110 = lean::cnstr_get(x_77, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_113 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_113 = x_77;
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_110);
lean::cnstr_set_scalar(x_114, sizeof(void*)*1, x_112);
x_115 = x_114;
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_115);
x_47 = x_116;
goto lbl_48;
}
}
else
{
obj* x_119; unsigned char x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_60);
lean::dec(x_66);
x_119 = lean::cnstr_get(x_67, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get_scalar<unsigned char>(x_67, sizeof(void*)*1);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_122 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_122 = x_67;
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_121);
x_124 = x_123;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_128; obj* x_130; obj* x_133; obj* x_135; 
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_125, 2);
lean::inc(x_130);
lean::dec(x_125);
x_133 = l_list_repr___main___rarg___closed__3;
lean::inc(x_133);
x_135 = l_lean_ir_symbol(x_133, x_128);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_136 = lean::cnstr_get(x_135, 1);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 2);
lean::inc(x_138);
lean::dec(x_135);
x_141 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_141, 0, x_126);
x_142 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_142);
if (lean::is_scalar(x_58)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_58;
}
lean::cnstr_set(x_144, 0, x_141);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_142);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_138, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_130, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_146);
x_47 = x_147;
goto lbl_48;
}
else
{
obj* x_150; unsigned char x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_58);
lean::dec(x_126);
x_150 = lean::cnstr_get(x_135, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get_scalar<unsigned char>(x_135, sizeof(void*)*1);
if (lean::is_shared(x_135)) {
 lean::dec(x_135);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_135, 0);
 x_153 = x_135;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_150);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = x_154;
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_130, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_156);
x_47 = x_157;
goto lbl_48;
}
}
else
{
obj* x_159; unsigned char x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
lean::dec(x_58);
x_159 = lean::cnstr_get(x_125, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get_scalar<unsigned char>(x_125, sizeof(void*)*1);
if (lean::is_shared(x_125)) {
 lean::dec(x_125);
 x_162 = lean::box(0);
} else {
 lean::cnstr_release(x_125, 0);
 x_162 = x_125;
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_159);
lean::cnstr_set_scalar(x_163, sizeof(void*)*1, x_161);
x_164 = x_163;
x_165 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_164);
x_47 = x_165;
goto lbl_48;
}
}
}
else
{
obj* x_167; unsigned char x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_58);
x_167 = lean::cnstr_get(x_59, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get_scalar<unsigned char>(x_59, sizeof(void*)*1);
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_170 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 x_170 = x_59;
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_167);
lean::cnstr_set_scalar(x_171, sizeof(void*)*1, x_169);
x_172 = x_171;
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_172);
x_47 = x_173;
goto lbl_48;
}
}
else
{
obj* x_174; unsigned char x_176; obj* x_177; obj* x_178; obj* x_179; 
x_174 = lean::cnstr_get(x_53, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get_scalar<unsigned char>(x_53, sizeof(void*)*1);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_177 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_177 = x_53;
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_174);
lean::cnstr_set_scalar(x_178, sizeof(void*)*1, x_176);
x_179 = x_178;
x_47 = x_179;
goto lbl_48;
}
}
else
{
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_40);
return x_12;
}
lbl_46:
{
obj* x_186; 
x_186 = l_lean_ir_parse__decl(x_44);
if (lean::obj_tag(x_186) == 0)
{
obj* x_187; obj* x_189; obj* x_191; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_186, 2);
lean::inc(x_191);
lean::dec(x_186);
if (lean::obj_tag(x_43) == 0)
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_43);
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_187);
lean::cnstr_set(x_195, 1, x_1);
x_196 = l_lean_ir_parse__input__aux___main(x_8, x_195, x_2, x_189);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_196);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_198);
return x_199;
}
else
{
obj* x_200; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_200 = lean::cnstr_get(x_43, 0);
lean::inc(x_200);
lean::dec(x_43);
lean::inc(x_187);
x_204 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_204, 0, x_187);
lean::cnstr_set(x_204, 1, x_1);
x_205 = l_lean_ir_decl_name(x_187);
x_206 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_205, x_200);
x_207 = l_lean_ir_parse__input__aux___main(x_8, x_204, x_206, x_189);
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_207);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_208);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_209);
return x_210;
}
}
else
{
obj* x_215; unsigned char x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_43);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_215 = lean::cnstr_get(x_186, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get_scalar<unsigned char>(x_186, sizeof(void*)*1);
if (lean::is_shared(x_186)) {
 lean::dec(x_186);
 x_218 = lean::box(0);
} else {
 lean::cnstr_release(x_186, 0);
 x_218 = x_186;
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_215);
lean::cnstr_set_scalar(x_219, sizeof(void*)*1, x_217);
x_220 = x_219;
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_220);
x_222 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_221);
return x_222;
}
}
lbl_48:
{
obj* x_223; 
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_3);
x_223 = x_11;
goto lbl_224;
}
else
{
obj* x_226; unsigned char x_228; 
x_226 = lean::cnstr_get(x_47, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get_scalar<unsigned char>(x_47, sizeof(void*)*1);
if (x_228 == 0)
{
obj* x_230; obj* x_233; obj* x_235; obj* x_236; 
lean::dec(x_47);
x_230 = lean::cnstr_get(x_226, 2);
lean::inc(x_230);
lean::dec(x_226);
x_233 = l_mjoin___rarg___closed__1;
lean::inc(x_233);
x_235 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_235, 0, x_230);
lean::closure_set(x_235, 1, x_233);
x_236 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_236, 0, x_235);
x_43 = x_11;
x_44 = x_3;
x_45 = x_236;
goto lbl_46;
}
else
{
lean::dec(x_226);
lean::dec(x_3);
x_223 = x_11;
goto lbl_224;
}
}
lbl_224:
{
lean::dec(x_223);
if (lean::obj_tag(x_47) == 0)
{
obj* x_240; obj* x_242; obj* x_244; 
x_240 = lean::cnstr_get(x_47, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get(x_47, 1);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_47, 2);
lean::inc(x_244);
lean::dec(x_47);
x_43 = x_240;
x_44 = x_242;
x_45 = x_244;
goto lbl_46;
}
else
{
obj* x_250; unsigned char x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_250 = lean::cnstr_get(x_47, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get_scalar<unsigned char>(x_47, sizeof(void*)*1);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_253 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_253 = x_47;
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*1, x_252);
x_255 = x_254;
x_256 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_255);
return x_256;
}
}
}
}
}
}
else
{
obj* x_258; obj* x_259; obj* x_260; obj* x_262; 
lean::dec(x_0);
x_258 = l_list_reverse___rarg(x_1);
x_259 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_2);
x_260 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_260);
x_262 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_262, 0, x_259);
lean::cnstr_set(x_262, 1, x_3);
lean::cnstr_set(x_262, 2, x_260);
return x_262;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
unsigned char x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; unsigned x_13; obj* x_14; unsigned char x_16; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_16 = l_char_is__alphanum(x_13);
if (x_16 == 0)
{
obj* x_17; obj* x_18; unsigned char x_19; 
x_17 = lean::mk_nat_obj(95u);
x_18 = lean::mk_nat_obj(55296u);
x_19 = lean::nat_dec_lt(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_21; unsigned char x_22; 
x_21 = lean::mk_nat_obj(57343u);
x_22 = lean::nat_dec_lt(x_21, x_17);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_25; unsigned char x_26; 
lean::dec(x_17);
x_25 = lean::box_uint32(x_13);
x_26 = lean::nat_dec_eq(x_25, x_3);
lean::dec(x_3);
lean::dec(x_25);
if (x_26 == 0)
{
if (x_16 == 0)
{
obj* x_30; 
lean::dec(x_10);
x_30 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::box(0);
x_14 = x_31;
goto lbl_15;
}
}
else
{
obj* x_32; 
x_32 = lean::box(0);
x_14 = x_32;
goto lbl_15;
}
}
else
{
obj* x_33; unsigned char x_34; 
x_33 = lean::mk_nat_obj(1114112u);
x_34 = lean::nat_dec_lt(x_17, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_37; unsigned char x_38; 
lean::dec(x_17);
x_37 = lean::box_uint32(x_13);
x_38 = lean::nat_dec_eq(x_37, x_3);
lean::dec(x_3);
lean::dec(x_37);
if (x_38 == 0)
{
if (x_16 == 0)
{
obj* x_42; 
lean::dec(x_10);
x_42 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_42;
}
else
{
obj* x_43; 
x_43 = lean::box(0);
x_14 = x_43;
goto lbl_15;
}
}
else
{
obj* x_44; 
x_44 = lean::box(0);
x_14 = x_44;
goto lbl_15;
}
}
else
{
obj* x_46; unsigned char x_47; 
lean::dec(x_3);
x_46 = lean::box_uint32(x_13);
x_47 = lean::nat_dec_eq(x_46, x_17);
lean::dec(x_17);
lean::dec(x_46);
if (x_47 == 0)
{
if (x_16 == 0)
{
obj* x_51; 
lean::dec(x_10);
x_51 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_51;
}
else
{
obj* x_52; 
x_52 = lean::box(0);
x_14 = x_52;
goto lbl_15;
}
}
else
{
obj* x_53; 
x_53 = lean::box(0);
x_14 = x_53;
goto lbl_15;
}
}
}
}
else
{
obj* x_55; unsigned char x_56; 
lean::dec(x_3);
x_55 = lean::box_uint32(x_13);
x_56 = lean::nat_dec_eq(x_55, x_17);
lean::dec(x_17);
lean::dec(x_55);
if (x_56 == 0)
{
if (x_16 == 0)
{
obj* x_60; 
lean::dec(x_10);
x_60 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::box(0);
x_14 = x_61;
goto lbl_15;
}
}
else
{
obj* x_62; 
x_62 = lean::box(0);
x_14 = x_62;
goto lbl_15;
}
}
}
else
{
lean::dec(x_3);
if (x_16 == 0)
{
obj* x_65; 
lean::dec(x_10);
x_65 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::box(0);
x_14 = x_66;
goto lbl_15;
}
}
lbl_15:
{
obj* x_68; obj* x_69; 
lean::dec(x_14);
x_68 = lean::string_push(x_1, x_13);
x_69 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_68;
x_2 = x_69;
goto _start;
}
}
}
else
{
obj* x_73; 
lean::dec(x_3);
lean::dec(x_0);
x_73 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_73;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(x_5, x_4, x_1);
return x_6;
}
}
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_3; 
x_3 = lean::string_iterator_has_next(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_10; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_5, x_6, x_4, x_4, x_0);
x_1 = x_10;
goto lbl_2;
}
else
{
unsigned x_11; obj* x_12; obj* x_14; unsigned char x_16; 
x_11 = lean::string_iterator_curr(x_0);
x_16 = l_char_is__alpha(x_11);
if (x_16 == 0)
{
obj* x_17; obj* x_18; unsigned char x_19; 
x_17 = lean::mk_nat_obj(95u);
x_18 = lean::mk_nat_obj(55296u);
x_19 = lean::nat_dec_lt(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_21; unsigned char x_22; 
x_21 = lean::mk_nat_obj(57343u);
x_22 = lean::nat_dec_lt(x_21, x_17);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_25; obj* x_26; unsigned char x_27; 
lean::dec(x_17);
x_25 = lean::mk_nat_obj(0u);
x_26 = lean::box_uint32(x_11);
x_27 = lean::nat_dec_eq(x_26, x_25);
lean::dec(x_25);
lean::dec(x_26);
if (x_27 == 0)
{
if (x_16 == 0)
{
obj* x_30; 
x_30 = lean::box(0);
x_12 = x_30;
goto lbl_13;
}
else
{
obj* x_31; 
x_31 = lean::box(0);
x_14 = x_31;
goto lbl_15;
}
}
else
{
obj* x_32; 
x_32 = lean::box(0);
x_14 = x_32;
goto lbl_15;
}
}
else
{
obj* x_33; unsigned char x_34; 
x_33 = lean::mk_nat_obj(1114112u);
x_34 = lean::nat_dec_lt(x_17, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_37; obj* x_38; unsigned char x_39; 
lean::dec(x_17);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean::box_uint32(x_11);
x_39 = lean::nat_dec_eq(x_38, x_37);
lean::dec(x_37);
lean::dec(x_38);
if (x_39 == 0)
{
if (x_16 == 0)
{
obj* x_42; 
x_42 = lean::box(0);
x_12 = x_42;
goto lbl_13;
}
else
{
obj* x_43; 
x_43 = lean::box(0);
x_14 = x_43;
goto lbl_15;
}
}
else
{
obj* x_44; 
x_44 = lean::box(0);
x_14 = x_44;
goto lbl_15;
}
}
else
{
obj* x_45; unsigned char x_46; 
x_45 = lean::box_uint32(x_11);
x_46 = lean::nat_dec_eq(x_45, x_17);
lean::dec(x_17);
lean::dec(x_45);
if (x_46 == 0)
{
if (x_16 == 0)
{
obj* x_49; 
x_49 = lean::box(0);
x_12 = x_49;
goto lbl_13;
}
else
{
obj* x_50; 
x_50 = lean::box(0);
x_14 = x_50;
goto lbl_15;
}
}
else
{
obj* x_51; 
x_51 = lean::box(0);
x_14 = x_51;
goto lbl_15;
}
}
}
}
else
{
obj* x_52; unsigned char x_53; 
x_52 = lean::box_uint32(x_11);
x_53 = lean::nat_dec_eq(x_52, x_17);
lean::dec(x_17);
lean::dec(x_52);
if (x_53 == 0)
{
if (x_16 == 0)
{
obj* x_56; 
x_56 = lean::box(0);
x_12 = x_56;
goto lbl_13;
}
else
{
obj* x_57; 
x_57 = lean::box(0);
x_14 = x_57;
goto lbl_15;
}
}
else
{
obj* x_58; 
x_58 = lean::box(0);
x_14 = x_58;
goto lbl_15;
}
}
}
else
{
if (x_16 == 0)
{
obj* x_59; 
x_59 = lean::box(0);
x_12 = x_59;
goto lbl_13;
}
else
{
obj* x_60; 
x_60 = lean::box(0);
x_14 = x_60;
goto lbl_15;
}
}
lbl_13:
{
obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_72; 
lean::dec(x_12);
x_62 = l_char_quote__core(x_11);
x_63 = l_char_has__repr___closed__1;
lean::inc(x_63);
x_65 = lean::string_append(x_63, x_62);
lean::dec(x_62);
x_67 = lean::string_append(x_65, x_63);
x_68 = lean::box(0);
x_69 = l_mjoin___rarg___closed__1;
lean::inc(x_68);
lean::inc(x_69);
x_72 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_67, x_69, x_68, x_68, x_0);
x_1 = x_72;
goto lbl_2;
}
lbl_15:
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_14);
x_74 = lean::string_iterator_next(x_0);
x_75 = lean::box(0);
x_76 = lean::box_uint32(x_11);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_74);
lean::cnstr_set(x_77, 2, x_75);
x_1 = x_77;
goto lbl_2;
}
}
lbl_2:
{
obj* x_78; obj* x_80; 
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_1);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_83; obj* x_85; unsigned x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_95; 
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_80, 2);
lean::inc(x_85);
lean::dec(x_80);
x_88 = lean::unbox_uint32(x_81);
lean::dec(x_81);
x_90 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_88, x_83);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_90);
x_92 = l_lean_parser_parsec__t_try__mk__res___rarg(x_91);
x_93 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_93);
x_95 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_92, x_93);
return x_95;
}
else
{
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_106; obj* x_108; unsigned char x_109; obj* x_110; obj* x_111; 
x_96 = lean::cnstr_get(x_80, 0);
lean::inc(x_96);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_98 = x_80;
}
x_99 = lean::cnstr_get(x_96, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_96, 1);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_96, 3);
lean::inc(x_103);
lean::dec(x_96);
x_106 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_106);
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_99);
lean::cnstr_set(x_108, 1, x_101);
lean::cnstr_set(x_108, 2, x_106);
lean::cnstr_set(x_108, 3, x_103);
x_109 = 0;
if (lean::is_scalar(x_98)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_98;
}
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_109);
x_111 = x_110;
return x_111;
}
}
}
}
obj* _init_l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_2, x_1);
return x_3;
}
}
obj* l_lean_ir_parse__input__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_parse__input(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_1 = lean::string_length(x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__input___lambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_3, x_0, x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_9 = x_6;
}
x_10 = l_lean_parser_parsec_message_to__string___rarg(x_7);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
}
}
obj* l_lean_ir_parse__input___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_ir_mk__fnid2string;
lean::inc(x_9);
x_11 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_9, x_4);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
return x_12;
}
else
{
obj* x_15; unsigned char x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_18 = x_3;
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_17);
x_20 = x_19;
return x_20;
}
}
}
obj* l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__whitespace(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; unsigned char x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_iterator_next(x_2);
x_18 = 1;
x_0 = x_14;
x_1 = x_18;
x_2 = x_17;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = 0;
x_3 = l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(x_1, x_2, x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(x_0);
return x_1;
}
}
obj* l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_1695453085__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_ir_check(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; 
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
}
x_12 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
else
{
obj* x_19; 
lean::dec(x_12);
lean::dec(x_11);
x_19 = l_lean_ir_var_declare___closed__1;
lean::inc(x_19);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::inc(x_2);
x_22 = l_lean_ir_decl_valid__ssa(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_27 = x_22;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_31; 
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
}
lean::inc(x_2);
x_31 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_31) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_0);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_29)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_29;
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_39; 
lean::dec(x_31);
x_39 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
lean::dec(x_39);
if (lean::is_scalar(x_29)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_29;
}
lean::cnstr_set(x_43, 0, x_40);
return x_43;
}
else
{
obj* x_46; 
lean::dec(x_29);
lean::dec(x_39);
x_46 = l_lean_ir_var_declare___closed__1;
lean::inc(x_46);
return x_46;
}
}
}
}
}
}
obj* l_lean_ir_check___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_check(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_ir_update__env(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_lean_ir_update__env___spec__4(x_3, x_0);
lean::inc(x_2);
x_6 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_4, x_2);
x_7 = lean::apply_1(x_1, x_2);
x_8 = l_option_orelse___main___rarg(x_6, x_7);
return x_8;
}
}
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
x_9 = l_lean_ir_decl_name(x_3);
x_10 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_9, x_3);
x_0 = x_10;
x_1 = x_5;
goto _start;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_11);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
lean::dec(x_9);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_35);
lean::inc(x_1);
x_44 = l_lean_name_quick__lt___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = l_lean_name_quick__lt___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_1);
lean::dec(x_39);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
lean::dec(x_37);
x_0 = x_39;
goto _start;
}
}
else
{
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_33;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_update__external__names(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_2);
x_5 = lean::apply_1(x_1, x_2);
x_6 = l_option_orelse___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_11);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
lean::dec(x_9);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_35);
lean::inc(x_1);
x_44 = l_lean_name_quick__lt___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = l_lean_name_quick__lt___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_1);
lean::dec(x_39);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
lean::dec(x_37);
x_0 = x_39;
goto _start;
}
}
else
{
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_33;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_lirc(obj* x_0, obj* x_1, unsigned char x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__input(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_20; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_11 = x_3;
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
lean::inc(x_12);
lean::inc(x_12);
lean::inc(x_1);
x_20 = l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(x_1, x_2, x_12, x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
if (lean::is_scalar(x_11)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_11;
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_46; 
lean::dec(x_11);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_1, 3);
lean::inc(x_30);
lean::inc(x_12);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_33, 0, x_12);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::cnstr_get(x_1, 4);
lean::inc(x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__external__names), 3, 2);
lean::closure_set(x_36, 0, x_14);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 2);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 5);
lean::inc(x_43);
lean::dec(x_1);
x_46 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set(x_46, 1, x_39);
lean::cnstr_set(x_46, 2, x_41);
lean::cnstr_set(x_46, 3, x_33);
lean::cnstr_set(x_46, 4, x_36);
lean::cnstr_set(x_46, 5, x_43);
if (x_2 == 0)
{
obj* x_47; 
x_47 = l_lean_ir_extract__cpp(x_12, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_list_map___main___at_lean_ir_lirc___spec__2(x_12);
x_49 = l_lean_ir_extract__cpp(x_48, x_46);
return x_49;
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_7 = l_lean_ir_var_declare___closed__1;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::cnstr_get(x_0, 3);
lean::inc(x_14);
lean::inc(x_2);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_17, 0, x_2);
lean::closure_set(x_17, 1, x_14);
x_18 = l_lean_ir_check(x_17, x_1, x_9);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_18, 0);
lean::inc(x_22);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_24 = x_18;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
return x_25;
}
else
{
lean::dec(x_18);
x_3 = x_11;
goto _start;
}
}
}
}
obj* l_list_map___main___at_lean_ir_lirc___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_lean_ir_elim__phi(x_3);
x_9 = l_list_map___main___at_lean_ir_lirc___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_lean_ir_lirc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_lean_ir_lirc(x_0, x_1, x_3);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
void initialize_init_lean_ir_parser();
void initialize_init_lean_ir_type__check();
void initialize_init_lean_ir_ssa__check();
void initialize_init_lean_ir_extract__cpp();
void initialize_init_lean_ir_format();
void initialize_init_lean_ir_elim__phi();
static bool _G_initialized = false;
void initialize_init_lean_ir_lirc() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_parser();
 initialize_init_lean_ir_type__check();
 initialize_init_lean_ir_ssa__check();
 initialize_init_lean_ir_extract__cpp();
 initialize_init_lean_ir_format();
 initialize_init_lean_ir_elim__phi();
 l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1 = _init_l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1();
}
