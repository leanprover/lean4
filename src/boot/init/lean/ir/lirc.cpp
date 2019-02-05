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
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_16; 
lean::dec(x_5);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_8);
lean::dec(x_0);
x_12 = lean::box(0);
lean::inc(x_3);
x_16 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 lean::cnstr_release(x_16, 2);
 x_21 = x_16;
}
lean::inc(x_1);
x_23 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_2);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_21;
}
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_17);
lean::cnstr_set(x_28, 2, x_26);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_13 = x_29;
goto lbl_14;
}
else
{
obj* x_30; unsigned char x_32; obj* x_33; obj* x_34; obj* x_35; 
x_30 = lean::cnstr_get(x_16, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<unsigned char>(x_16, sizeof(void*)*1);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_33 = x_16;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
x_13 = x_35;
goto lbl_14;
}
lbl_14:
{
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_12);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_13;
}
else
{
obj* x_41; unsigned char x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; 
x_41 = lean::cnstr_get(x_13, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get_scalar<unsigned char>(x_13, sizeof(void*)*1);
if (x_43 == 0)
{
obj* x_51; obj* x_54; 
lean::dec(x_13);
x_51 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_51);
x_54 = l_lean_ir_symbol(x_51, x_3);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 x_59 = x_54;
}
x_60 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_55);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; 
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 2);
lean::inc(x_65);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 lean::cnstr_release(x_60, 2);
 x_67 = x_60;
}
x_68 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_63);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 2);
lean::inc(x_71);
lean::dec(x_68);
x_74 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_74);
if (lean::is_scalar(x_59)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_59;
}
lean::cnstr_set(x_76, 0, x_61);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_74);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_88; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_list_repr___main___rarg___closed__3;
lean::inc(x_86);
x_88 = l_lean_ir_symbol(x_86, x_81);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_79);
lean::inc(x_74);
if (lean::is_scalar(x_67)) {
 x_96 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_96 = x_67;
}
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_89);
lean::cnstr_set(x_96, 2, x_74);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_96);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_98);
x_48 = x_99;
goto lbl_49;
}
else
{
obj* x_102; unsigned char x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_79);
lean::dec(x_67);
x_102 = lean::cnstr_get(x_88, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get_scalar<unsigned char>(x_88, sizeof(void*)*1);
if (lean::is_shared(x_88)) {
 lean::dec(x_88);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_88, 0);
 x_105 = x_88;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
x_107 = x_106;
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_108);
x_48 = x_109;
goto lbl_49;
}
}
else
{
obj* x_111; unsigned char x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_67);
x_111 = lean::cnstr_get(x_78, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get_scalar<unsigned char>(x_78, sizeof(void*)*1);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_114 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_114 = x_78;
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_111);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = x_115;
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_116);
x_48 = x_117;
goto lbl_49;
}
}
else
{
obj* x_120; unsigned char x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_61);
lean::dec(x_67);
x_120 = lean::cnstr_get(x_68, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get_scalar<unsigned char>(x_68, sizeof(void*)*1);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_123 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_123 = x_68;
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_122);
x_125 = x_124;
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_127; obj* x_129; obj* x_131; obj* x_134; obj* x_136; 
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 2);
lean::inc(x_131);
lean::dec(x_126);
x_134 = l_list_repr___main___rarg___closed__3;
lean::inc(x_134);
x_136 = l_lean_ir_symbol(x_134, x_129);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_139; obj* x_142; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_137 = lean::cnstr_get(x_136, 1);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_136, 2);
lean::inc(x_139);
lean::dec(x_136);
x_142 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_142, 0, x_127);
x_143 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_143);
if (lean::is_scalar(x_59)) {
 x_145 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_145 = x_59;
}
lean::cnstr_set(x_145, 0, x_142);
lean::cnstr_set(x_145, 1, x_137);
lean::cnstr_set(x_145, 2, x_143);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_139, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_131, x_146);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_147);
x_48 = x_148;
goto lbl_49;
}
else
{
obj* x_151; unsigned char x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_59);
lean::dec(x_127);
x_151 = lean::cnstr_get(x_136, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get_scalar<unsigned char>(x_136, sizeof(void*)*1);
if (lean::is_shared(x_136)) {
 lean::dec(x_136);
 x_154 = lean::box(0);
} else {
 lean::cnstr_release(x_136, 0);
 x_154 = x_136;
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set_scalar(x_155, sizeof(void*)*1, x_153);
x_156 = x_155;
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_131, x_156);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_157);
x_48 = x_158;
goto lbl_49;
}
}
else
{
obj* x_160; unsigned char x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_59);
x_160 = lean::cnstr_get(x_126, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get_scalar<unsigned char>(x_126, sizeof(void*)*1);
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_163 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_163 = x_126;
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_160);
lean::cnstr_set_scalar(x_164, sizeof(void*)*1, x_162);
x_165 = x_164;
x_166 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_165);
x_48 = x_166;
goto lbl_49;
}
}
}
else
{
obj* x_168; unsigned char x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_59);
x_168 = lean::cnstr_get(x_60, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get_scalar<unsigned char>(x_60, sizeof(void*)*1);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_171 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_171 = x_60;
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set_scalar(x_172, sizeof(void*)*1, x_170);
x_173 = x_172;
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_173);
x_48 = x_174;
goto lbl_49;
}
}
else
{
obj* x_175; unsigned char x_177; obj* x_178; obj* x_179; obj* x_180; 
x_175 = lean::cnstr_get(x_54, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get_scalar<unsigned char>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_178 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_178 = x_54;
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_175);
lean::cnstr_set_scalar(x_179, sizeof(void*)*1, x_177);
x_180 = x_179;
x_48 = x_180;
goto lbl_49;
}
}
else
{
lean::dec(x_12);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_41);
return x_13;
}
lbl_47:
{
obj* x_187; 
x_187 = l_lean_ir_parse__decl(x_45);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_190; obj* x_192; 
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_187, 2);
lean::inc(x_192);
lean::dec(x_187);
if (lean::obj_tag(x_44) == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
lean::dec(x_44);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_188);
lean::cnstr_set(x_196, 1, x_1);
x_197 = l_lean_ir_parse__input__aux___main(x_9, x_196, x_2, x_190);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_197);
x_199 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_198);
x_200 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_199);
return x_200;
}
else
{
obj* x_201; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_201 = lean::cnstr_get(x_44, 0);
lean::inc(x_201);
lean::dec(x_44);
lean::inc(x_188);
x_205 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_205, 0, x_188);
lean::cnstr_set(x_205, 1, x_1);
x_206 = l_lean_ir_decl_name(x_188);
x_207 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_206, x_201);
x_208 = l_lean_ir_parse__input__aux___main(x_9, x_205, x_207, x_190);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_208);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_209);
x_211 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_210);
return x_211;
}
}
else
{
obj* x_216; unsigned char x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
lean::dec(x_44);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_2);
x_216 = lean::cnstr_get(x_187, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get_scalar<unsigned char>(x_187, sizeof(void*)*1);
if (lean::is_shared(x_187)) {
 lean::dec(x_187);
 x_219 = lean::box(0);
} else {
 lean::cnstr_release(x_187, 0);
 x_219 = x_187;
}
if (lean::is_scalar(x_219)) {
 x_220 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_220 = x_219;
}
lean::cnstr_set(x_220, 0, x_216);
lean::cnstr_set_scalar(x_220, sizeof(void*)*1, x_218);
x_221 = x_220;
x_222 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_221);
x_223 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_222);
return x_223;
}
}
lbl_49:
{
obj* x_224; 
if (lean::obj_tag(x_48) == 0)
{
lean::dec(x_3);
x_224 = x_12;
goto lbl_225;
}
else
{
obj* x_227; unsigned char x_229; 
x_227 = lean::cnstr_get(x_48, 0);
lean::inc(x_227);
x_229 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
if (x_229 == 0)
{
obj* x_231; obj* x_234; obj* x_236; obj* x_237; 
lean::dec(x_48);
x_231 = lean::cnstr_get(x_227, 2);
lean::inc(x_231);
lean::dec(x_227);
x_234 = l_mjoin___rarg___closed__1;
lean::inc(x_234);
x_236 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_236, 0, x_231);
lean::closure_set(x_236, 1, x_234);
x_237 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_237, 0, x_236);
x_44 = x_12;
x_45 = x_3;
x_46 = x_237;
goto lbl_47;
}
else
{
lean::dec(x_227);
lean::dec(x_3);
x_224 = x_12;
goto lbl_225;
}
}
lbl_225:
{
lean::dec(x_224);
if (lean::obj_tag(x_48) == 0)
{
obj* x_241; obj* x_243; obj* x_245; 
x_241 = lean::cnstr_get(x_48, 0);
lean::inc(x_241);
x_243 = lean::cnstr_get(x_48, 1);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_48, 2);
lean::inc(x_245);
lean::dec(x_48);
x_44 = x_241;
x_45 = x_243;
x_46 = x_245;
goto lbl_47;
}
else
{
obj* x_251; unsigned char x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_2);
x_251 = lean::cnstr_get(x_48, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_254 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_254 = x_48;
}
if (lean::is_scalar(x_254)) {
 x_255 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_255 = x_254;
}
lean::cnstr_set(x_255, 0, x_251);
lean::cnstr_set_scalar(x_255, sizeof(void*)*1, x_253);
x_256 = x_255;
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_256);
return x_257;
}
}
}
}
}
}
else
{
obj* x_260; obj* x_261; obj* x_262; obj* x_264; 
lean::dec(x_5);
lean::dec(x_0);
x_260 = l_list_reverse___rarg(x_1);
x_261 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_261, 0, x_260);
lean::cnstr_set(x_261, 1, x_2);
x_262 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_262);
x_264 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_264, 0, x_261);
lean::cnstr_set(x_264, 1, x_3);
lean::cnstr_set(x_264, 2, x_262);
return x_264;
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
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_6; 
lean::dec(x_4);
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; obj* x_15; unsigned char x_17; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_10);
lean::dec(x_0);
x_14 = lean::string_iterator_curr(x_2);
x_17 = l_char_is__alphanum(x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::mk_nat_obj(95u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_20);
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_18);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_18);
lean::dec(x_24);
x_28 = lean::box_uint32(x_14);
x_29 = lean::nat_dec_eq(x_28, x_3);
lean::dec(x_3);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_29);
if (x_17 == 0)
{
obj* x_34; 
lean::dec(x_11);
x_34 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_34;
}
else
{
obj* x_35; 
x_35 = lean::box(0);
x_15 = x_35;
goto lbl_16;
}
}
else
{
obj* x_37; 
lean::dec(x_29);
x_37 = lean::box(0);
x_15 = x_37;
goto lbl_16;
}
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_24);
x_39 = lean::mk_nat_obj(1114112u);
x_40 = lean::nat_dec_lt(x_18, x_39);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_18);
lean::dec(x_40);
x_44 = lean::box_uint32(x_14);
x_45 = lean::nat_dec_eq(x_44, x_3);
lean::dec(x_3);
lean::dec(x_44);
if (lean::obj_tag(x_45) == 0)
{
lean::dec(x_45);
if (x_17 == 0)
{
obj* x_50; 
lean::dec(x_11);
x_50 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_50;
}
else
{
obj* x_51; 
x_51 = lean::box(0);
x_15 = x_51;
goto lbl_16;
}
}
else
{
obj* x_53; 
lean::dec(x_45);
x_53 = lean::box(0);
x_15 = x_53;
goto lbl_16;
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_3);
lean::dec(x_40);
x_56 = lean::box_uint32(x_14);
x_57 = lean::nat_dec_eq(x_56, x_18);
lean::dec(x_18);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
lean::dec(x_57);
if (x_17 == 0)
{
obj* x_62; 
lean::dec(x_11);
x_62 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_62;
}
else
{
obj* x_63; 
x_63 = lean::box(0);
x_15 = x_63;
goto lbl_16;
}
}
else
{
obj* x_65; 
lean::dec(x_57);
x_65 = lean::box(0);
x_15 = x_65;
goto lbl_16;
}
}
}
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_20);
lean::dec(x_3);
x_68 = lean::box_uint32(x_14);
x_69 = lean::nat_dec_eq(x_68, x_18);
lean::dec(x_18);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
lean::dec(x_69);
if (x_17 == 0)
{
obj* x_74; 
lean::dec(x_11);
x_74 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_74;
}
else
{
obj* x_75; 
x_75 = lean::box(0);
x_15 = x_75;
goto lbl_16;
}
}
else
{
obj* x_77; 
lean::dec(x_69);
x_77 = lean::box(0);
x_15 = x_77;
goto lbl_16;
}
}
}
else
{
lean::dec(x_3);
if (x_17 == 0)
{
obj* x_80; 
lean::dec(x_11);
x_80 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::box(0);
x_15 = x_81;
goto lbl_16;
}
}
lbl_16:
{
obj* x_83; obj* x_84; 
lean::dec(x_15);
x_83 = lean::string_push(x_1, x_14);
x_84 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_83;
x_2 = x_84;
goto _start;
}
}
}
else
{
obj* x_89; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_89 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_89;
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
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::mk_nat_obj(95u);
x_18 = lean::mk_nat_obj(55296u);
x_19 = lean::nat_dec_lt(x_17, x_18);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_19);
x_22 = lean::mk_nat_obj(57343u);
x_23 = lean::nat_dec_lt(x_22, x_17);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_17);
lean::dec(x_23);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::box_uint32(x_11);
x_29 = lean::nat_dec_eq(x_28, x_27);
lean::dec(x_27);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_29);
if (x_16 == 0)
{
obj* x_33; 
x_33 = lean::box(0);
x_12 = x_33;
goto lbl_13;
}
else
{
obj* x_34; 
x_34 = lean::box(0);
x_14 = x_34;
goto lbl_15;
}
}
else
{
obj* x_36; 
lean::dec(x_29);
x_36 = lean::box(0);
x_14 = x_36;
goto lbl_15;
}
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_23);
x_38 = lean::mk_nat_obj(1114112u);
x_39 = lean::nat_dec_lt(x_17, x_38);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_17);
lean::dec(x_39);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::box_uint32(x_11);
x_45 = lean::nat_dec_eq(x_44, x_43);
lean::dec(x_43);
lean::dec(x_44);
if (lean::obj_tag(x_45) == 0)
{
lean::dec(x_45);
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
obj* x_52; 
lean::dec(x_45);
x_52 = lean::box(0);
x_14 = x_52;
goto lbl_15;
}
}
else
{
obj* x_54; obj* x_55; 
lean::dec(x_39);
x_54 = lean::box_uint32(x_11);
x_55 = lean::nat_dec_eq(x_54, x_17);
lean::dec(x_17);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
lean::dec(x_55);
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
else
{
obj* x_62; 
lean::dec(x_55);
x_62 = lean::box(0);
x_14 = x_62;
goto lbl_15;
}
}
}
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_19);
x_64 = lean::box_uint32(x_11);
x_65 = lean::nat_dec_eq(x_64, x_17);
lean::dec(x_17);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 0)
{
lean::dec(x_65);
if (x_16 == 0)
{
obj* x_69; 
x_69 = lean::box(0);
x_12 = x_69;
goto lbl_13;
}
else
{
obj* x_70; 
x_70 = lean::box(0);
x_14 = x_70;
goto lbl_15;
}
}
else
{
obj* x_72; 
lean::dec(x_65);
x_72 = lean::box(0);
x_14 = x_72;
goto lbl_15;
}
}
}
else
{
if (x_16 == 0)
{
obj* x_73; 
x_73 = lean::box(0);
x_12 = x_73;
goto lbl_13;
}
else
{
obj* x_74; 
x_74 = lean::box(0);
x_14 = x_74;
goto lbl_15;
}
}
lbl_13:
{
obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_86; 
lean::dec(x_12);
x_76 = l_char_quote__core(x_11);
x_77 = l_char_has__repr___closed__1;
lean::inc(x_77);
x_79 = lean::string_append(x_77, x_76);
lean::dec(x_76);
x_81 = lean::string_append(x_79, x_77);
x_82 = lean::box(0);
x_83 = l_mjoin___rarg___closed__1;
lean::inc(x_82);
lean::inc(x_83);
x_86 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_81, x_83, x_82, x_82, x_0);
x_1 = x_86;
goto lbl_2;
}
lbl_15:
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_14);
x_88 = lean::string_iterator_next(x_0);
x_89 = lean::box(0);
x_90 = lean::box_uint32(x_11);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_89);
x_1 = x_91;
goto lbl_2;
}
}
lbl_2:
{
obj* x_92; obj* x_94; 
x_92 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_1);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_97; obj* x_99; unsigned x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_109; 
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_94, 2);
lean::inc(x_99);
lean::dec(x_94);
x_102 = lean::unbox_uint32(x_95);
lean::dec(x_95);
x_104 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_102, x_97);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_99, x_104);
x_106 = l_lean_parser_parsec__t_try__mk__res___rarg(x_105);
x_107 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_107);
x_109 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_106, x_107);
return x_109;
}
else
{
obj* x_110; obj* x_112; obj* x_113; obj* x_115; obj* x_117; obj* x_120; obj* x_122; unsigned char x_123; obj* x_124; obj* x_125; 
x_110 = lean::cnstr_get(x_94, 0);
lean::inc(x_110);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_112 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_112 = x_94;
}
x_113 = lean::cnstr_get(x_110, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_110, 3);
lean::inc(x_117);
lean::dec(x_110);
x_120 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_120);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_113);
lean::cnstr_set(x_122, 1, x_115);
lean::cnstr_set(x_122, 2, x_120);
lean::cnstr_set(x_122, 3, x_117);
x_123 = 0;
if (lean::is_scalar(x_112)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_112;
}
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_123);
x_125 = x_124;
return x_125;
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
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_7; 
lean::dec(x_4);
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_0);
x_9 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__whitespace(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; unsigned char x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_iterator_next(x_2);
x_19 = 1;
x_0 = x_15;
x_1 = x_19;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_23;
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
