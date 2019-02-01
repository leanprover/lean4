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
#endif
obj* _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_elim__phi(obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5(unsigned, obj*);
unsigned char _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_var_s7_declare_s11___closed__1;
obj* _l_s4_lean_s2_ir_s5_check(obj*, unsigned char, obj*);
obj* _l_s4_lean_s2_ir_s11_type__check(obj*, obj*);
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__4(obj*, obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s15_check__blockids(obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
obj* _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3(obj*, unsigned char, obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2;
obj* _l_s4_char_s11_quote__core(unsigned);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1(obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1;
obj* _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s2_ir_s4_lirc_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s12_parse__input_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(obj*, obj*);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s4_decl_s4_name(obj*);
unsigned char _l_s4_char_s12_is__alphanum(unsigned);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__1(obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s9___private_1496486805__s27_parse__mangled__string__aux_s6___main_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s4_lirc(obj*, obj*, unsigned char);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4(obj*);
unsigned char _l_s4_char_s9_is__alpha(unsigned);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj*, obj*);
obj* _l_s4_char_s9_has__repr_s11___closed__1;
obj* _l_s4_lean_s2_ir_s23_update__external__names(obj*, obj*, obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5_s7___boxed(obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3_s7___boxed(obj*, obj*, obj*);
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__5(obj*, obj*);
obj* _l_s4_lean_s2_ir_s6_symbol(obj*, obj*);
obj* _l_s4_list_s7_reverse_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s9___private_1496486805__s27_parse__mangled__string__aux_s6___main_s9___spec__6(obj*);
obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6(obj*);
obj* _l_s4_lean_s2_ir_s12_parse__input(obj*);
obj* _l_s4_list_s3_map_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__2(obj*);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(obj*, obj*);
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s2_ir_s15_mk__fnid2string;
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
obj* _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(unsigned char, obj*);
unsigned char _l_s4_char_s14_is__whitespace(unsigned);
obj* _l_s4_lean_s2_ir_s12_extract__cpp(obj*, obj*);
obj* _l_s4_lean_s2_ir_s4_decl_s10_valid__ssa(obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_check_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s4___at_s4_lean_s2_ir_s6_symbol_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s11_parse__decl(obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__6(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_update__env(obj*, obj*, obj*);
obj* _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s2_ir_s17_parse__input__aux(obj*, obj*, obj*, obj*);
obj* _l_s6_option_s6_orelse_s6___main_s6___rarg(obj*, obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__2(obj*);
obj* _l_s5_dlist_s9_singleton_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_12 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_3);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s9___private_1496486805__s27_parse__mangled__string__aux_s6___main_s9___spec__6(x_3);
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
x_23 = _l_s4_list_s7_reverse_s6___rarg(x_1);
lean::inc(x_2);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_2);
x_26 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_21;
}
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_17);
lean::cnstr_set(x_28, 2, x_26);
x_29 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_19, x_28);
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
lean::dec(x_2);
lean::dec(x_3);
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
x_51 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2;
lean::inc(x_3);
lean::inc(x_51);
x_54 = _l_s4_lean_s2_ir_s6_symbol(x_51, x_3);
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
x_60 = _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4(x_55);
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
x_68 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s4___at_s4_lean_s2_ir_s6_symbol_s9___spec__2(x_63);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 2);
lean::inc(x_71);
lean::dec(x_68);
x_74 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_74);
if (lean::is_scalar(x_59)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_59;
}
lean::cnstr_set(x_76, 0, x_61);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_74);
x_77 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_71, x_76);
x_78 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_65, x_77);
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
x_86 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
lean::inc(x_86);
x_88 = _l_s4_lean_s2_ir_s6_symbol(x_86, x_81);
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
x_97 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_91, x_96);
x_98 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_83, x_97);
x_99 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_98);
x_48 = x_99;
goto lbl_49;
}
else
{
obj* x_103; unsigned char x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_67);
lean::dec(x_79);
lean::dec(x_74);
x_103 = lean::cnstr_get(x_88, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<unsigned char>(x_88, sizeof(void*)*1);
if (lean::is_shared(x_88)) {
 lean::dec(x_88);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_88, 0);
 x_106 = x_88;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_109 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_83, x_108);
x_110 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_109);
x_48 = x_110;
goto lbl_49;
}
}
else
{
obj* x_113; unsigned char x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_67);
lean::dec(x_74);
x_113 = lean::cnstr_get(x_78, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<unsigned char>(x_78, sizeof(void*)*1);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_116 = x_78;
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
x_119 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_118);
x_48 = x_119;
goto lbl_49;
}
}
else
{
obj* x_122; unsigned char x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_67);
lean::dec(x_61);
x_122 = lean::cnstr_get(x_68, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get_scalar<unsigned char>(x_68, sizeof(void*)*1);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_125 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_125 = x_68;
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set_scalar(x_126, sizeof(void*)*1, x_124);
x_127 = x_126;
x_128 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_65, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_129; obj* x_131; obj* x_133; obj* x_136; obj* x_138; 
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 2);
lean::inc(x_133);
lean::dec(x_128);
x_136 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
lean::inc(x_136);
x_138 = _l_s4_lean_s2_ir_s6_symbol(x_136, x_131);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_141; obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 2);
lean::inc(x_141);
lean::dec(x_138);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_129);
x_145 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_145);
if (lean::is_scalar(x_59)) {
 x_147 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_147 = x_59;
}
lean::cnstr_set(x_147, 0, x_144);
lean::cnstr_set(x_147, 1, x_139);
lean::cnstr_set(x_147, 2, x_145);
x_148 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_141, x_147);
x_149 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_133, x_148);
x_150 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_149);
x_48 = x_150;
goto lbl_49;
}
else
{
obj* x_153; unsigned char x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_129);
lean::dec(x_59);
x_153 = lean::cnstr_get(x_138, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get_scalar<unsigned char>(x_138, sizeof(void*)*1);
if (lean::is_shared(x_138)) {
 lean::dec(x_138);
 x_156 = lean::box(0);
} else {
 lean::cnstr_release(x_138, 0);
 x_156 = x_138;
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_153);
lean::cnstr_set_scalar(x_157, sizeof(void*)*1, x_155);
x_158 = x_157;
x_159 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_133, x_158);
x_160 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_159);
x_48 = x_160;
goto lbl_49;
}
}
else
{
obj* x_162; unsigned char x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_59);
x_162 = lean::cnstr_get(x_128, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get_scalar<unsigned char>(x_128, sizeof(void*)*1);
if (lean::is_shared(x_128)) {
 lean::dec(x_128);
 x_165 = lean::box(0);
} else {
 lean::cnstr_release(x_128, 0);
 x_165 = x_128;
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_162);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_164);
x_167 = x_166;
x_168 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_167);
x_48 = x_168;
goto lbl_49;
}
}
}
else
{
obj* x_170; unsigned char x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_59);
x_170 = lean::cnstr_get(x_60, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get_scalar<unsigned char>(x_60, sizeof(void*)*1);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_173 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_173 = x_60;
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_170);
lean::cnstr_set_scalar(x_174, sizeof(void*)*1, x_172);
x_175 = x_174;
x_176 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_57, x_175);
x_48 = x_176;
goto lbl_49;
}
}
else
{
obj* x_177; unsigned char x_179; obj* x_180; obj* x_181; obj* x_182; 
x_177 = lean::cnstr_get(x_54, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get_scalar<unsigned char>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_180 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_180 = x_54;
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_177);
lean::cnstr_set_scalar(x_181, sizeof(void*)*1, x_179);
x_182 = x_181;
x_48 = x_182;
goto lbl_49;
}
}
else
{

lean::dec(x_12);
lean::dec(x_41);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_13;
}
lbl_47:
{
obj* x_189; 
x_189 = _l_s4_lean_s2_ir_s11_parse__decl(x_45);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; obj* x_192; obj* x_194; 
x_190 = lean::cnstr_get(x_189, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_189, 2);
lean::inc(x_194);
lean::dec(x_189);
if (lean::obj_tag(x_44) == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
lean::dec(x_44);
x_198 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_198, 0, x_190);
lean::cnstr_set(x_198, 1, x_1);
x_199 = _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(x_9, x_198, x_2, x_192);
x_200 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_194, x_199);
x_201 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_46, x_200);
x_202 = _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(x_41, x_201);
return x_202;
}
else
{
obj* x_203; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
x_203 = lean::cnstr_get(x_44, 0);
lean::inc(x_203);
lean::dec(x_44);
lean::inc(x_190);
x_207 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_207, 0, x_190);
lean::cnstr_set(x_207, 1, x_1);
x_208 = _l_s4_lean_s2_ir_s4_decl_s4_name(x_190);
x_209 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__2(x_2, x_208, x_203);
x_210 = _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(x_9, x_207, x_209, x_192);
x_211 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_194, x_210);
x_212 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_46, x_211);
x_213 = _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(x_41, x_212);
return x_213;
}
}
else
{
obj* x_218; unsigned char x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
lean::dec(x_44);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_2);
x_218 = lean::cnstr_get(x_189, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<unsigned char>(x_189, sizeof(void*)*1);
if (lean::is_shared(x_189)) {
 lean::dec(x_189);
 x_221 = lean::box(0);
} else {
 lean::cnstr_release(x_189, 0);
 x_221 = x_189;
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_218);
lean::cnstr_set_scalar(x_222, sizeof(void*)*1, x_220);
x_223 = x_222;
x_224 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_46, x_223);
x_225 = _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(x_41, x_224);
return x_225;
}
}
lbl_49:
{
unsigned char x_226; 
if (lean::obj_tag(x_48) == 0)
{
unsigned char x_230; 
lean::dec(x_12);
lean::dec(x_3);
x_230 = 0;
x_226 = x_230;
goto lbl_227;
}
else
{
obj* x_231; unsigned char x_233; 
x_231 = lean::cnstr_get(x_48, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
if (x_233 == 0)
{
obj* x_235; obj* x_238; obj* x_240; obj* x_241; 
lean::dec(x_48);
x_235 = lean::cnstr_get(x_231, 2);
lean::inc(x_235);
lean::dec(x_231);
x_238 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_238);
x_240 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_240, 0, x_235);
lean::closure_set(x_240, 1, x_238);
x_241 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_241, 0, x_240);
x_44 = x_12;
x_45 = x_3;
x_46 = x_241;
goto lbl_47;
}
else
{
unsigned char x_245; 
lean::dec(x_231);
lean::dec(x_12);
lean::dec(x_3);
x_245 = 0;
x_226 = x_245;
goto lbl_227;
}
}
lbl_227:
{

if (lean::obj_tag(x_48) == 0)
{
obj* x_246; obj* x_248; obj* x_250; 
x_246 = lean::cnstr_get(x_48, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_48, 1);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_48, 2);
lean::inc(x_250);
lean::dec(x_48);
x_44 = x_246;
x_45 = x_248;
x_46 = x_250;
goto lbl_47;
}
else
{
obj* x_256; unsigned char x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_2);
x_256 = lean::cnstr_get(x_48, 0);
lean::inc(x_256);
x_258 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_259 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_259 = x_48;
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_256);
lean::cnstr_set_scalar(x_260, sizeof(void*)*1, x_258);
x_261 = x_260;
x_262 = _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(x_41, x_261);
return x_262;
}
}
}
}
}
}
else
{
obj* x_265; obj* x_266; obj* x_267; obj* x_269; 
lean::dec(x_5);
lean::dec(x_0);
x_265 = _l_s4_list_s7_reverse_s6___rarg(x_1);
x_266 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_2);
x_267 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_267);
x_269 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_269, 0, x_266);
lean::cnstr_set(x_269, 1, x_3);
lean::cnstr_set(x_269, 2, x_267);
return x_269;
}
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_7);
lean::dec(x_9);
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
x_27 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_11, x_1, x_2);
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
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_5, x_1, x_2);
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
x_42 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_35);
lean::dec(x_33);
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
x_54 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_37, x_1, x_2);
x_57 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_37, x_1, x_2);
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
x_61 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_31, x_1, x_2);
x_64 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_31, x_1, x_2);
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
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__3(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__6(obj* x_0, obj* x_1, obj* x_2) {
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
lean::dec(x_0);
lean::dec(x_3);
x_9 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; unsigned char x_15; unsigned char x_17; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_10);
lean::dec(x_0);
x_14 = lean::string_iterator_curr(x_2);
x_17 = _l_s4_char_s12_is__alphanum(x_14);
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
x_34 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_34;
}
else
{
unsigned char x_35; 
x_35 = 0;
x_15 = x_35;
goto lbl_16;
}
}
else
{
unsigned char x_37; 
lean::dec(x_29);
x_37 = 0;
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
lean::dec(x_40);
lean::dec(x_18);
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
x_50 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_50;
}
else
{
unsigned char x_51; 
x_51 = 0;
x_15 = x_51;
goto lbl_16;
}
}
else
{
unsigned char x_53; 
lean::dec(x_45);
x_53 = 0;
x_15 = x_53;
goto lbl_16;
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_40);
lean::dec(x_3);
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
x_62 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_62;
}
else
{
unsigned char x_63; 
x_63 = 0;
x_15 = x_63;
goto lbl_16;
}
}
else
{
unsigned char x_65; 
lean::dec(x_57);
x_65 = 0;
x_15 = x_65;
goto lbl_16;
}
}
}
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_3);
lean::dec(x_20);
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
x_74 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_74;
}
else
{
unsigned char x_75; 
x_75 = 0;
x_15 = x_75;
goto lbl_16;
}
}
else
{
unsigned char x_77; 
lean::dec(x_69);
x_77 = 0;
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
x_80 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_80;
}
else
{
unsigned char x_81; 
x_81 = 0;
x_15 = x_81;
goto lbl_16;
}
}
lbl_16:
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::string_push(x_1, x_14);
x_83 = lean::string_iterator_next(x_2);
x_84 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__6(x_11, x_82, x_83);
return x_84;
}
}
}
else
{
obj* x_88; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_3);
x_88 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_88;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5(unsigned x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__6(x_5, x_4, x_1);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4(obj* x_0) {
{
obj* x_1; unsigned char x_3; 
x_3 = lean::string_iterator_has_next(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_10; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_6 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s9___private_1496486805__s27_parse__mangled__string__aux_s6___main_s9___spec__3_s6___rarg(x_5, x_6, x_4, x_4, x_0);
x_1 = x_10;
goto lbl_2;
}
else
{
unsigned x_11; unsigned char x_12; unsigned char x_14; unsigned char x_16; 
x_11 = lean::string_iterator_curr(x_0);
x_16 = _l_s4_char_s9_is__alpha(x_11);
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
unsigned char x_33; 
x_33 = 0;
x_12 = x_33;
goto lbl_13;
}
else
{
unsigned char x_34; 
x_34 = 0;
x_14 = x_34;
goto lbl_15;
}
}
else
{
unsigned char x_36; 
lean::dec(x_29);
x_36 = 0;
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
unsigned char x_49; 
x_49 = 0;
x_12 = x_49;
goto lbl_13;
}
else
{
unsigned char x_50; 
x_50 = 0;
x_14 = x_50;
goto lbl_15;
}
}
else
{
unsigned char x_52; 
lean::dec(x_45);
x_52 = 0;
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
unsigned char x_59; 
x_59 = 0;
x_12 = x_59;
goto lbl_13;
}
else
{
unsigned char x_60; 
x_60 = 0;
x_14 = x_60;
goto lbl_15;
}
}
else
{
unsigned char x_62; 
lean::dec(x_55);
x_62 = 0;
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
unsigned char x_69; 
x_69 = 0;
x_12 = x_69;
goto lbl_13;
}
else
{
unsigned char x_70; 
x_70 = 0;
x_14 = x_70;
goto lbl_15;
}
}
else
{
unsigned char x_72; 
lean::dec(x_65);
x_72 = 0;
x_14 = x_72;
goto lbl_15;
}
}
}
else
{

if (x_16 == 0)
{
unsigned char x_73; 
x_73 = 0;
x_12 = x_73;
goto lbl_13;
}
else
{
unsigned char x_74; 
x_74 = 0;
x_14 = x_74;
goto lbl_15;
}
}
lbl_13:
{
obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_85; 
x_75 = _l_s4_char_s11_quote__core(x_11);
x_76 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_76);
x_78 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_80 = lean::string_append(x_78, x_76);
x_81 = lean::alloc_cnstr(0, 0, 0);
;
x_82 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_81);
lean::inc(x_82);
x_85 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s9___private_1496486805__s27_parse__mangled__string__aux_s6___main_s9___spec__3_s6___rarg(x_80, x_82, x_81, x_81, x_0);
x_1 = x_85;
goto lbl_2;
}
lbl_15:
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_86 = lean::string_iterator_next(x_0);
x_87 = lean::alloc_cnstr(0, 0, 0);
;
x_88 = lean::box_uint32(x_11);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_86);
lean::cnstr_set(x_89, 2, x_87);
x_1 = x_89;
goto lbl_2;
}
}
lbl_2:
{
obj* x_90; obj* x_92; 
x_90 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_90);
x_92 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_90, x_1);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_95; obj* x_97; unsigned x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_107; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 2);
lean::inc(x_97);
lean::dec(x_92);
x_100 = lean::unbox_uint32(x_93);
lean::dec(x_93);
x_102 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5(x_100, x_95);
x_103 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_97, x_102);
x_104 = _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg(x_103);
x_105 = _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1;
lean::inc(x_105);
x_107 = _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(x_104, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_110; obj* x_111; obj* x_113; obj* x_115; obj* x_118; obj* x_120; unsigned char x_121; obj* x_122; obj* x_123; 
x_108 = lean::cnstr_get(x_92, 0);
lean::inc(x_108);
if (lean::is_shared(x_92)) {
 lean::dec(x_92);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_92, 0);
 x_110 = x_92;
}
x_111 = lean::cnstr_get(x_108, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_108, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_108, 3);
lean::inc(x_115);
lean::dec(x_108);
x_118 = _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1;
lean::inc(x_118);
x_120 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_120, 0, x_111);
lean::cnstr_set(x_120, 1, x_113);
lean::cnstr_set(x_120, 2, x_118);
lean::cnstr_set(x_120, 3, x_115);
x_121 = 0;
if (lean::is_scalar(x_110)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_110;
}
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_121);
x_123 = x_122;
return x_123;
}
}
}
}
obj* _init__l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__5(x_2, x_1);
return x_3;
}
}
obj* _l_s4_lean_s2_ir_s17_parse__input__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s12_parse__input(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_1 = lean::string_length(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s12_parse__input_s11___lambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg(x_3, x_0, x_4);
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
x_10 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg(x_7);
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
obj* _l_s4_lean_s2_ir_s12_parse__input_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__1(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = _l_s4_lean_s2_ir_s15_mk__fnid2string;
lean::inc(x_9);
x_11 = _l_s4_lean_s2_ir_s17_parse__input__aux_s6___main(x_0, x_1, x_9, x_4);
x_12 = _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(x_6, x_11);
return x_12;
}
else
{
obj* x_15; unsigned char x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_0);
lean::dec(x_1);
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
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3(obj* x_0, unsigned char x_1, obj* x_2) {
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
x_9 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = _l_s4_char_s14_is__whitespace(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; unsigned char x_19; obj* x_20; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_iterator_next(x_2);
x_19 = 1;
x_20 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3(x_15, x_19, x_18);
return x_20;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_23;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__2(obj* x_0) {
{
obj* x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = 0;
x_3 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3(x_1, x_2, x_0);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__1(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__2(x_0);
return x_1;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s2_ir_s12_parse__input_s9___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s5_check(obj* x_0, unsigned char x_1, obj* x_2) {
{

if (x_1 == 0)
{
obj* x_4; 
lean::inc(x_2);
x_4 = _l_s4_lean_s2_ir_s15_check__blockids(x_2);
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
x_12 = _l_s4_lean_s2_ir_s11_type__check(x_2, x_0);
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
lean::dec(x_11);
lean::dec(x_12);
x_19 = _l_s4_lean_s2_ir_s3_var_s7_declare_s11___closed__1;
lean::inc(x_19);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::inc(x_2);
x_22 = _l_s4_lean_s2_ir_s4_decl_s10_valid__ssa(x_2);
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
x_31 = _l_s4_lean_s2_ir_s15_check__blockids(x_2);
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
x_39 = _l_s4_lean_s2_ir_s11_type__check(x_2, x_0);
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
x_46 = _l_s4_lean_s2_ir_s3_var_s7_declare_s11___closed__1;
lean::inc(x_46);
return x_46;
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s5_check_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s4_lean_s2_ir_s5_check(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s11_update__env(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::alloc_cnstr(0, 0, 0);
;
x_4 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__4(x_3, x_0);
lean::inc(x_2);
x_6 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_4, x_2);
x_7 = lean::apply_1(x_1, x_2);
x_8 = _l_s6_option_s6_orelse_s6___main_s6___rarg(x_6, x_7);
return x_8;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_7);
lean::dec(x_9);
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
x_27 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_11, x_1, x_2);
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
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_5, x_1, x_2);
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
x_42 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_35);
lean::dec(x_33);
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
x_54 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_37, x_1, x_2);
x_57 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_37, x_1, x_2);
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
x_61 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_31, x_1, x_2);
x_64 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_31, x_1, x_2);
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
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__3(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__4(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{

lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_3);
x_9 = _l_s4_lean_s2_ir_s4_decl_s4_name(x_3);
x_10 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__2(x_0, x_9, x_3);
x_11 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__4(x_10, x_5);
return x_11;
}
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(obj* x_0, obj* x_1) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
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
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_9);
x_28 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_11, x_1);
return x_28;
}
}
else
{
obj* x_32; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_32 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_5, x_1);
return x_32;
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
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_39);
lean::dec(x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
obj* x_56; 
lean::dec(x_37);
x_56 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_39, x_1);
return x_56;
}
}
else
{
obj* x_60; 
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_60 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_33, x_1);
return x_60;
}
}
}
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__5(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s11_update__env_s9___spec__6_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s23_update__external__names(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_0, x_2);
x_5 = lean::apply_1(x_1, x_2);
x_6 = _l_s6_option_s6_orelse_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(obj* x_0, obj* x_1) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
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
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_9);
x_28 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_11, x_1);
return x_28;
}
}
else
{
obj* x_32; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_32 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_5, x_1);
return x_32;
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
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_39);
lean::dec(x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
obj* x_56; 
lean::dec(x_37);
x_56 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_39, x_1);
return x_56;
}
}
else
{
obj* x_60; 
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_60 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_33, x_1);
return x_60;
}
}
}
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s23_update__external__names_s9___spec__2_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s4_lirc(obj* x_0, obj* x_1, unsigned char x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s12_parse__input(x_0);
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
x_20 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1(x_1, x_2, x_12, x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_12);
lean::dec(x_14);
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
x_33 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s11_update__env), 3, 2);
lean::closure_set(x_33, 0, x_12);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::cnstr_get(x_1, 4);
lean::inc(x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s23_update__external__names), 3, 2);
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
x_47 = _l_s4_lean_s2_ir_s12_extract__cpp(x_12, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = _l_s4_list_s3_map_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__2(x_12);
x_49 = _l_s4_lean_s2_ir_s12_extract__cpp(x_48, x_46);
return x_49;
}
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_7 = _l_s4_lean_s2_ir_s3_var_s7_declare_s11___closed__1;
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
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s11_update__env), 3, 2);
lean::closure_set(x_17, 0, x_2);
lean::closure_set(x_17, 1, x_14);
x_18 = _l_s4_lean_s2_ir_s5_check(x_17, x_1, x_9);
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
obj* x_27; 
lean::dec(x_18);
x_27 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1(x_0, x_1, x_2, x_11);
return x_27;
}
}
}
}
obj* _l_s4_list_s3_map_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__2(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
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
x_8 = _l_s4_lean_s2_ir_s9_elim__phi(x_3);
x_9 = _l_s4_list_s3_map_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__2(x_5);
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
obj* _l_s4_lean_s2_ir_s4_lirc_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s4_lean_s2_ir_s4_lirc(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_lirc_s9___spec__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
void _l_initialize__l_s4_init_s4_lean_s2_ir_s6_parser();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s11_type__check();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s10_ssa__check();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s12_extract__cpp();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s6_format();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s9_elim__phi();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s2_ir_s4_lirc() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s2_ir_s6_parser();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s11_type__check();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s10_ssa__check();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s12_extract__cpp();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s6_format();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s9_elim__phi();
 _l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_c__identifier_s4___at_s4_lean_s2_ir_s17_parse__input__aux_s6___main_s9___spec__4_s11___closed__1();
}
