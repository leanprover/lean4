// Lean compiler output
// Module: init.lean.name_mangling
// Imports: init.lean.name init.lean.parser.string_literal
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
obj* l_lean_string_demangle___closed__1;
obj* l_nat_digit__char(obj*);
obj* l_match__failed___at___private_4217055689__parse__mangled__name__aux___main___spec__19(obj*);
obj* l___private_4217055689__parse__mangled__name__aux(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_name_demangle(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10(unsigned, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6___boxed(obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__7(obj*, obj*, obj*);
obj* l___private_74862231__parse__mangled__name(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__17(obj*, obj*, obj*);
obj* l___private_1205956357__name_mangle__aux___main(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10___boxed(obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l___private_3255790009__string_mangle__aux___main___closed__2;
extern obj* l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
unsigned char l_char_is__digit(unsigned);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l___private_1205956357__name_mangle__aux(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at___private_1496486805__parse__mangled__string__aux___main___spec__4(obj*);
unsigned char l_string_is__empty(obj*);
unsigned char l_char_is__alpha(unsigned);
obj* l_lean_parser_monad__parsec_alpha___at___private_1496486805__parse__mangled__string__aux___main___spec__5(obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l___private_1496486805__parse__mangled__string__aux___main(obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1;
obj* l___private_580269747__str__aux___main(obj*, obj*, obj*);
obj* l___private_3255790009__string_mangle__aux___main___closed__1;
obj* l_lean_name_mangle(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__15(obj*, obj*, obj*);
obj* l_lean_string_mangle(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14(unsigned, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_string_to__nat(obj*);
extern obj* l_char_has__repr___closed__1;
obj* l___private_3162311557__parse__mangled__string(obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__11(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_id___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3(obj*);
obj* l___private_1496486805__parse__mangled__string__aux___main___closed__2;
obj* l___private_4217055689__parse__mangled__name__aux___main___closed__1;
obj* l___private_4217055689__parse__mangled__name__aux___main(obj*, obj*, obj*);
obj* l___private_127590107__take__aux___main___rarg(obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__5(obj*, obj*, obj*);
obj* l___private_1496486805__parse__mangled__string__aux___main___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4(unsigned, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6(unsigned, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1___boxed(obj*, obj*);
obj* l___private_3255790009__string_mangle__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8(unsigned, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take___at___private_4217055689__parse__mangled__name__aux___main___spec__18(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(unsigned, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at___private_4217055689__parse__mangled__name__aux___main___spec__3(obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12(unsigned, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4___boxed(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(obj*);
obj* l_nat_repr(obj*);
extern obj* l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__16(obj*, obj*);
obj* l___private_1496486805__parse__mangled__string__aux___main___closed__3;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12___boxed(obj*, obj*);
obj* l___private_1205956357__name_mangle__aux___main___closed__1;
obj* l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
obj* l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(obj*, obj*, obj*);
obj* l___private_3255790009__string_mangle__aux(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
extern obj* l_match__failed___rarg___closed__1;
obj* l_lean_string_demangle(obj*);
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__13(obj*, obj*, obj*);
obj* l___private_1496486805__parse__mangled__string__aux(obj*, obj*, obj*);
obj* l___private_3255790009__string_mangle__aux___main___closed__3;
obj* l_char_quote__core(unsigned);
obj* l___private_1205956357__name_mangle__aux___main___closed__2;
obj* l___private_3255790009__string_mangle__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; unsigned x_10; obj* x_11; obj* x_13; unsigned char x_15; 
lean::dec(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::string_iterator_curr(x_1);
x_15 = l_char_is__alpha(x_10);
if (x_15 == 0)
{
unsigned char x_16; 
x_16 = l_char_is__digit(x_10);
if (x_16 == 0)
{
obj* x_17; 
x_17 = lean::box(0);
x_13 = x_17;
goto lbl_14;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_3);
x_19 = lean::string_iterator_next(x_1);
x_20 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
else
{
if (x_15 == 0)
{
obj* x_22; 
x_22 = lean::box(0);
x_13 = x_22;
goto lbl_14;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_3);
x_24 = lean::string_iterator_next(x_1);
x_25 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_24;
x_2 = x_25;
goto _start;
}
}
lbl_12:
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_11);
x_28 = lean::mk_nat_obj(255u);
x_29 = lean::box_uint32(x_10);
x_30 = lean::nat_dec_lt(x_29, x_28);
lean::dec(x_28);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; unsigned x_38; obj* x_40; obj* x_41; obj* x_44; obj* x_45; obj* x_46; unsigned x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; unsigned x_56; obj* x_58; obj* x_59; obj* x_62; unsigned x_63; obj* x_65; obj* x_66; 
lean::dec(x_30);
x_33 = l___private_3255790009__string_mangle__aux___main___closed__1;
x_34 = lean::string_append(x_2, x_33);
x_35 = lean::mk_nat_obj(4096u);
x_36 = lean::nat_div(x_29, x_35);
x_37 = l_nat_digit__char(x_36);
x_38 = lean::unbox_uint32(x_37);
lean::dec(x_37);
x_40 = lean::string_push(x_34, x_38);
x_41 = lean::nat_mod(x_29, x_35);
lean::dec(x_35);
lean::dec(x_29);
x_44 = lean::mk_nat_obj(256u);
x_45 = lean::nat_div(x_41, x_44);
x_46 = l_nat_digit__char(x_45);
x_47 = lean::unbox_uint32(x_46);
lean::dec(x_46);
x_49 = lean::string_push(x_40, x_47);
x_50 = lean::nat_mod(x_41, x_44);
lean::dec(x_44);
lean::dec(x_41);
x_53 = lean::mk_nat_obj(16u);
x_54 = lean::nat_div(x_50, x_53);
x_55 = l_nat_digit__char(x_54);
x_56 = lean::unbox_uint32(x_55);
lean::dec(x_55);
x_58 = lean::string_push(x_49, x_56);
x_59 = lean::nat_mod(x_50, x_53);
lean::dec(x_53);
lean::dec(x_50);
x_62 = l_nat_digit__char(x_59);
x_63 = lean::unbox_uint32(x_62);
lean::dec(x_62);
x_65 = lean::string_push(x_58, x_63);
x_66 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_66;
x_2 = x_65;
goto _start;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; unsigned x_74; obj* x_76; obj* x_77; obj* x_80; unsigned x_81; obj* x_83; obj* x_84; 
lean::dec(x_30);
x_69 = l___private_3255790009__string_mangle__aux___main___closed__2;
x_70 = lean::string_append(x_2, x_69);
x_71 = lean::mk_nat_obj(16u);
x_72 = lean::nat_div(x_29, x_71);
x_73 = l_nat_digit__char(x_72);
x_74 = lean::unbox_uint32(x_73);
lean::dec(x_73);
x_76 = lean::string_push(x_70, x_74);
x_77 = lean::nat_mod(x_29, x_71);
lean::dec(x_71);
lean::dec(x_29);
x_80 = l_nat_digit__char(x_77);
x_81 = lean::unbox_uint32(x_80);
lean::dec(x_80);
x_83 = lean::string_push(x_76, x_81);
x_84 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_84;
x_2 = x_83;
goto _start;
}
}
lbl_14:
{
obj* x_87; obj* x_88; obj* x_89; unsigned x_91; 
lean::dec(x_13);
x_87 = lean::mk_nat_obj(95u);
x_88 = lean::mk_nat_obj(55296u);
x_89 = lean::nat_dec_lt(x_87, x_88);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_94; obj* x_95; 
lean::dec(x_89);
x_94 = lean::mk_nat_obj(57343u);
x_95 = lean::nat_dec_lt(x_94, x_87);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
unsigned x_99; 
lean::dec(x_87);
lean::dec(x_95);
x_99 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_91 = x_99;
goto lbl_92;
}
else
{
obj* x_102; obj* x_103; 
lean::dec(x_95);
x_102 = lean::mk_nat_obj(1114112u);
x_103 = lean::nat_dec_lt(x_87, x_102);
lean::dec(x_102);
if (lean::obj_tag(x_103) == 0)
{
unsigned x_107; 
lean::dec(x_87);
lean::dec(x_103);
x_107 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_91 = x_107;
goto lbl_92;
}
else
{
unsigned x_111; 
lean::dec(x_3);
lean::dec(x_103);
x_111 = lean::unbox_uint32(x_87);
lean::dec(x_87);
x_91 = x_111;
goto lbl_92;
}
}
}
else
{
unsigned x_115; 
lean::dec(x_3);
lean::dec(x_89);
x_115 = lean::unbox_uint32(x_87);
lean::dec(x_87);
x_91 = x_115;
goto lbl_92;
}
lbl_92:
{
obj* x_117; obj* x_118; obj* x_119; 
x_117 = lean::box_uint32(x_10);
x_118 = lean::box_uint32(x_91);
x_119 = lean::nat_dec_eq(x_117, x_118);
lean::dec(x_118);
lean::dec(x_117);
if (lean::obj_tag(x_119) == 0)
{
obj* x_123; 
lean::dec(x_119);
x_123 = lean::box(0);
x_11 = x_123;
goto lbl_12;
}
else
{
obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_119);
x_125 = lean::string_iterator_next(x_1);
x_126 = l___private_3255790009__string_mangle__aux___main___closed__3;
x_127 = lean::string_append(x_2, x_126);
x_0 = x_7;
x_1 = x_125;
x_2 = x_127;
goto _start;
}
}
}
}
else
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* _init_l___private_3255790009__string_mangle__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_u");
return x_0;
}
}
obj* _init_l___private_3255790009__string_mangle__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_x");
return x_0;
}
}
obj* _init_l___private_3255790009__string_mangle__aux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("__");
return x_0;
}
}
obj* l___private_3255790009__string_mangle__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_3255790009__string_mangle__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_string_mangle(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_3255790009__string_mangle__aux___main(x_1, x_2, x_3);
return x_5;
}
}
obj* l___private_1496486805__parse__mangled__string__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_13; 
lean::dec(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
lean::inc(x_2);
x_13 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 lean::cnstr_release(x_13, 2);
 x_18 = x_13;
}
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_19);
lean::inc(x_1);
if (lean::is_scalar(x_18)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_18;
}
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_14);
lean::cnstr_set(x_22, 2, x_19);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_22);
x_10 = x_23;
goto lbl_11;
}
else
{
obj* x_24; unsigned char x_26; obj* x_27; obj* x_28; obj* x_29; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<unsigned char>(x_13, sizeof(void*)*1);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_27 = x_13;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_26);
x_29 = x_28;
x_10 = x_29;
goto lbl_11;
}
lbl_11:
{
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_34; unsigned char x_36; obj* x_37; obj* x_38; unsigned char x_39; 
x_34 = lean::cnstr_get(x_10, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_43; 
lean::dec(x_10);
lean::inc(x_2);
x_43 = l_lean_parser_monad__parsec_alpha___at___private_1496486805__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_46; obj* x_48; unsigned x_51; obj* x_54; obj* x_56; obj* x_57; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 2);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::unbox_uint32(x_44);
lean::dec(x_44);
lean::inc(x_1);
x_54 = lean::string_push(x_1, x_51);
lean::inc(x_7);
x_56 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_54, x_46);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_62; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_62 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_57);
return x_62;
}
else
{
obj* x_63; unsigned char x_65; 
x_63 = lean::cnstr_get(x_57, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
x_37 = x_57;
x_38 = x_63;
x_39 = x_65;
goto lbl_40;
}
}
else
{
obj* x_66; unsigned char x_68; obj* x_69; obj* x_71; obj* x_72; 
x_66 = lean::cnstr_get(x_43, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get_scalar<unsigned char>(x_43, sizeof(void*)*1);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 x_69 = x_43;
}
lean::inc(x_66);
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_66);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_68);
x_72 = x_71;
x_37 = x_72;
x_38 = x_66;
x_39 = x_68;
goto lbl_40;
}
}
else
{
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_34);
return x_10;
}
lbl_40:
{
obj* x_78; obj* x_79; unsigned char x_80; 
if (x_39 == 0)
{
obj* x_84; 
lean::dec(x_37);
lean::inc(x_2);
x_84 = l_lean_parser_monad__parsec_digit___at___private_1496486805__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; obj* x_87; obj* x_89; unsigned x_92; obj* x_95; obj* x_97; obj* x_98; 
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_84, 2);
lean::inc(x_89);
lean::dec(x_84);
x_92 = lean::unbox_uint32(x_85);
lean::dec(x_85);
lean::inc(x_1);
x_95 = lean::string_push(x_1, x_92);
lean::inc(x_7);
x_97 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_95, x_87);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_103 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_98);
x_104 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_103);
return x_104;
}
else
{
obj* x_105; unsigned char x_107; 
x_105 = lean::cnstr_get(x_98, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get_scalar<unsigned char>(x_98, sizeof(void*)*1);
x_78 = x_98;
x_79 = x_105;
x_80 = x_107;
goto lbl_81;
}
}
else
{
obj* x_108; unsigned char x_110; obj* x_111; obj* x_113; obj* x_114; 
x_108 = lean::cnstr_get(x_84, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get_scalar<unsigned char>(x_84, sizeof(void*)*1);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 x_111 = x_84;
}
lean::inc(x_108);
if (lean::is_scalar(x_111)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_111;
}
lean::cnstr_set(x_113, 0, x_108);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_110);
x_114 = x_113;
x_78 = x_114;
x_79 = x_108;
x_80 = x_110;
goto lbl_81;
}
}
else
{
obj* x_120; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_38);
x_120 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_37);
return x_120;
}
lbl_81:
{
obj* x_121; obj* x_122; unsigned char x_123; 
if (x_80 == 0)
{
obj* x_126; obj* x_127; obj* x_131; 
lean::dec(x_78);
x_126 = l___private_3255790009__string_mangle__aux___main___closed__3;
x_127 = l___private_1496486805__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
lean::inc(x_127);
lean::inc(x_126);
x_131 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_126, x_127, x_2);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; obj* x_134; obj* x_137; obj* x_138; obj* x_139; 
x_132 = lean::cnstr_get(x_131, 1);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 2);
lean::inc(x_134);
lean::dec(x_131);
x_137 = lean::mk_nat_obj(95u);
x_138 = lean::mk_nat_obj(55296u);
x_139 = lean::nat_dec_lt(x_137, x_138);
lean::dec(x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_142; obj* x_143; 
lean::dec(x_139);
x_142 = lean::mk_nat_obj(57343u);
x_143 = lean::nat_dec_lt(x_142, x_137);
lean::dec(x_142);
if (lean::obj_tag(x_143) == 0)
{
unsigned x_147; obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_137);
lean::dec(x_143);
x_147 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_149 = lean::string_push(x_1, x_147);
lean::inc(x_7);
x_151 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_149, x_132);
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_157 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_152);
x_158 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_157);
x_159 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_158);
return x_159;
}
else
{
obj* x_160; unsigned char x_162; 
x_160 = lean::cnstr_get(x_152, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get_scalar<unsigned char>(x_152, sizeof(void*)*1);
x_121 = x_152;
x_122 = x_160;
x_123 = x_162;
goto lbl_124;
}
}
else
{
obj* x_164; obj* x_165; 
lean::dec(x_143);
x_164 = lean::mk_nat_obj(1114112u);
x_165 = lean::nat_dec_lt(x_137, x_164);
lean::dec(x_164);
if (lean::obj_tag(x_165) == 0)
{
unsigned x_169; obj* x_171; obj* x_173; obj* x_174; 
lean::dec(x_165);
lean::dec(x_137);
x_169 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_171 = lean::string_push(x_1, x_169);
lean::inc(x_7);
x_173 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_171, x_132);
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_173);
if (lean::obj_tag(x_174) == 0)
{
obj* x_179; obj* x_180; obj* x_181; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_179 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_174);
x_180 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_179);
x_181 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_180);
return x_181;
}
else
{
obj* x_182; unsigned char x_184; 
x_182 = lean::cnstr_get(x_174, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get_scalar<unsigned char>(x_174, sizeof(void*)*1);
x_121 = x_174;
x_122 = x_182;
x_123 = x_184;
goto lbl_124;
}
}
else
{
unsigned x_186; obj* x_189; obj* x_191; obj* x_192; 
lean::dec(x_165);
x_186 = lean::unbox_uint32(x_137);
lean::dec(x_137);
lean::inc(x_1);
x_189 = lean::string_push(x_1, x_186);
lean::inc(x_7);
x_191 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_189, x_132);
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_191);
if (lean::obj_tag(x_192) == 0)
{
obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_197 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_192);
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_198);
return x_199;
}
else
{
obj* x_200; unsigned char x_202; 
x_200 = lean::cnstr_get(x_192, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get_scalar<unsigned char>(x_192, sizeof(void*)*1);
x_121 = x_192;
x_122 = x_200;
x_123 = x_202;
goto lbl_124;
}
}
}
}
else
{
unsigned x_204; obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_139);
x_204 = lean::unbox_uint32(x_137);
lean::dec(x_137);
lean::inc(x_1);
x_207 = lean::string_push(x_1, x_204);
lean::inc(x_7);
x_209 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_207, x_132);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_215 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_210);
x_216 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_215);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_216);
return x_217;
}
else
{
obj* x_218; unsigned char x_220; 
x_218 = lean::cnstr_get(x_210, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<unsigned char>(x_210, sizeof(void*)*1);
x_121 = x_210;
x_122 = x_218;
x_123 = x_220;
goto lbl_124;
}
}
}
else
{
obj* x_221; unsigned char x_223; obj* x_224; obj* x_226; obj* x_227; 
x_221 = lean::cnstr_get(x_131, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get_scalar<unsigned char>(x_131, sizeof(void*)*1);
if (lean::is_shared(x_131)) {
 lean::dec(x_131);
 x_224 = lean::box(0);
} else {
 lean::cnstr_release(x_131, 0);
 x_224 = x_131;
}
lean::inc(x_221);
if (lean::is_scalar(x_224)) {
 x_226 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_226 = x_224;
}
lean::cnstr_set(x_226, 0, x_221);
lean::cnstr_set_scalar(x_226, sizeof(void*)*1, x_223);
x_227 = x_226;
x_121 = x_227;
x_122 = x_221;
x_123 = x_223;
goto lbl_124;
}
}
else
{
obj* x_233; obj* x_234; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_79);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_78);
x_234 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_233);
return x_234;
}
lbl_124:
{
obj* x_235; obj* x_236; unsigned char x_237; 
if (x_123 == 0)
{
obj* x_240; obj* x_241; obj* x_245; 
lean::dec(x_121);
x_240 = l___private_3255790009__string_mangle__aux___main___closed__2;
x_241 = l___private_1496486805__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_241);
lean::inc(x_240);
x_245 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_240, x_241, x_2);
if (lean::obj_tag(x_245) == 0)
{
obj* x_246; obj* x_248; obj* x_251; 
x_246 = lean::cnstr_get(x_245, 1);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 2);
lean::inc(x_248);
lean::dec(x_245);
x_251 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_246);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_254; obj* x_256; obj* x_259; 
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_251, 2);
lean::inc(x_256);
lean::dec(x_251);
x_259 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_254);
if (lean::obj_tag(x_259) == 0)
{
obj* x_260; obj* x_262; obj* x_264; obj* x_267; obj* x_268; obj* x_271; obj* x_274; obj* x_275; 
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_259, 1);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_259, 2);
lean::inc(x_264);
lean::dec(x_259);
x_267 = lean::mk_nat_obj(16u);
x_268 = lean::nat_mul(x_252, x_267);
lean::dec(x_267);
lean::dec(x_252);
x_271 = lean::nat_add(x_268, x_260);
lean::dec(x_260);
lean::dec(x_268);
x_274 = lean::mk_nat_obj(55296u);
x_275 = lean::nat_dec_lt(x_271, x_274);
lean::dec(x_274);
if (lean::obj_tag(x_275) == 0)
{
obj* x_278; obj* x_279; 
lean::dec(x_275);
x_278 = lean::mk_nat_obj(57343u);
x_279 = lean::nat_dec_lt(x_278, x_271);
lean::dec(x_278);
if (lean::obj_tag(x_279) == 0)
{
unsigned x_283; obj* x_285; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
lean::dec(x_271);
lean::dec(x_279);
x_283 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_285 = lean::string_push(x_1, x_283);
lean::inc(x_7);
x_287 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_285, x_262);
x_288 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_287);
x_289 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_288);
x_290 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_289);
if (lean::obj_tag(x_290) == 0)
{
obj* x_295; obj* x_296; obj* x_297; obj* x_298; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_295 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_290);
x_296 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_295);
x_297 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_296);
x_298 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_297);
return x_298;
}
else
{
obj* x_299; unsigned char x_301; 
x_299 = lean::cnstr_get(x_290, 0);
lean::inc(x_299);
x_301 = lean::cnstr_get_scalar<unsigned char>(x_290, sizeof(void*)*1);
x_235 = x_290;
x_236 = x_299;
x_237 = x_301;
goto lbl_238;
}
}
else
{
obj* x_303; obj* x_304; 
lean::dec(x_279);
x_303 = lean::mk_nat_obj(1114112u);
x_304 = lean::nat_dec_lt(x_271, x_303);
lean::dec(x_303);
if (lean::obj_tag(x_304) == 0)
{
unsigned x_308; obj* x_310; obj* x_312; obj* x_313; obj* x_314; obj* x_315; 
lean::dec(x_271);
lean::dec(x_304);
x_308 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_310 = lean::string_push(x_1, x_308);
lean::inc(x_7);
x_312 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_310, x_262);
x_313 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_312);
x_314 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_313);
x_315 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_314);
if (lean::obj_tag(x_315) == 0)
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_320 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_315);
x_321 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_320);
x_322 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_321);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_322);
return x_323;
}
else
{
obj* x_324; unsigned char x_326; 
x_324 = lean::cnstr_get(x_315, 0);
lean::inc(x_324);
x_326 = lean::cnstr_get_scalar<unsigned char>(x_315, sizeof(void*)*1);
x_235 = x_315;
x_236 = x_324;
x_237 = x_326;
goto lbl_238;
}
}
else
{
unsigned x_328; obj* x_331; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_304);
x_328 = lean::unbox_uint32(x_271);
lean::dec(x_271);
lean::inc(x_1);
x_331 = lean::string_push(x_1, x_328);
lean::inc(x_7);
x_333 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_331, x_262);
x_334 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_333);
x_335 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_334);
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_335);
if (lean::obj_tag(x_336) == 0)
{
obj* x_341; obj* x_342; obj* x_343; obj* x_344; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_336);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_341);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_343);
return x_344;
}
else
{
obj* x_345; unsigned char x_347; 
x_345 = lean::cnstr_get(x_336, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get_scalar<unsigned char>(x_336, sizeof(void*)*1);
x_235 = x_336;
x_236 = x_345;
x_237 = x_347;
goto lbl_238;
}
}
}
}
else
{
unsigned x_349; obj* x_352; obj* x_354; obj* x_355; obj* x_356; obj* x_357; 
lean::dec(x_275);
x_349 = lean::unbox_uint32(x_271);
lean::dec(x_271);
lean::inc(x_1);
x_352 = lean::string_push(x_1, x_349);
lean::inc(x_7);
x_354 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_352, x_262);
x_355 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_354);
x_356 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_355);
x_357 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_356);
if (lean::obj_tag(x_357) == 0)
{
obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_362 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_357);
x_363 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_362);
x_364 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_363);
x_365 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_364);
return x_365;
}
else
{
obj* x_366; unsigned char x_368; 
x_366 = lean::cnstr_get(x_357, 0);
lean::inc(x_366);
x_368 = lean::cnstr_get_scalar<unsigned char>(x_357, sizeof(void*)*1);
x_235 = x_357;
x_236 = x_366;
x_237 = x_368;
goto lbl_238;
}
}
}
else
{
obj* x_370; unsigned char x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
lean::dec(x_252);
x_370 = lean::cnstr_get(x_259, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get_scalar<unsigned char>(x_259, sizeof(void*)*1);
if (lean::is_shared(x_259)) {
 lean::dec(x_259);
 x_373 = lean::box(0);
} else {
 lean::cnstr_release(x_259, 0);
 x_373 = x_259;
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_370);
lean::cnstr_set_scalar(x_374, sizeof(void*)*1, x_372);
x_375 = x_374;
x_376 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_375);
x_377 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_376);
if (lean::obj_tag(x_377) == 0)
{
obj* x_382; obj* x_383; obj* x_384; obj* x_385; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_382 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_377);
x_383 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_382);
x_384 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_383);
x_385 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_384);
return x_385;
}
else
{
obj* x_386; unsigned char x_388; 
x_386 = lean::cnstr_get(x_377, 0);
lean::inc(x_386);
x_388 = lean::cnstr_get_scalar<unsigned char>(x_377, sizeof(void*)*1);
x_235 = x_377;
x_236 = x_386;
x_237 = x_388;
goto lbl_238;
}
}
}
else
{
obj* x_389; unsigned char x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; 
x_389 = lean::cnstr_get(x_251, 0);
lean::inc(x_389);
x_391 = lean::cnstr_get_scalar<unsigned char>(x_251, sizeof(void*)*1);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_392 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_392 = x_251;
}
if (lean::is_scalar(x_392)) {
 x_393 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_393 = x_392;
}
lean::cnstr_set(x_393, 0, x_389);
lean::cnstr_set_scalar(x_393, sizeof(void*)*1, x_391);
x_394 = x_393;
x_395 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_394);
if (lean::obj_tag(x_395) == 0)
{
obj* x_400; obj* x_401; obj* x_402; obj* x_403; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_400 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_395);
x_401 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_400);
x_402 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_401);
x_403 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_402);
return x_403;
}
else
{
obj* x_404; unsigned char x_406; 
x_404 = lean::cnstr_get(x_395, 0);
lean::inc(x_404);
x_406 = lean::cnstr_get_scalar<unsigned char>(x_395, sizeof(void*)*1);
x_235 = x_395;
x_236 = x_404;
x_237 = x_406;
goto lbl_238;
}
}
}
else
{
obj* x_407; unsigned char x_409; obj* x_410; obj* x_412; obj* x_413; 
x_407 = lean::cnstr_get(x_245, 0);
lean::inc(x_407);
x_409 = lean::cnstr_get_scalar<unsigned char>(x_245, sizeof(void*)*1);
if (lean::is_shared(x_245)) {
 lean::dec(x_245);
 x_410 = lean::box(0);
} else {
 lean::cnstr_release(x_245, 0);
 x_410 = x_245;
}
lean::inc(x_407);
if (lean::is_scalar(x_410)) {
 x_412 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_412 = x_410;
}
lean::cnstr_set(x_412, 0, x_407);
lean::cnstr_set_scalar(x_412, sizeof(void*)*1, x_409);
x_413 = x_412;
x_235 = x_413;
x_236 = x_407;
x_237 = x_409;
goto lbl_238;
}
}
else
{
obj* x_419; obj* x_420; obj* x_421; 
lean::dec(x_122);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_121);
x_420 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_419);
x_421 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_420);
return x_421;
}
lbl_238:
{
if (x_237 == 0)
{
obj* x_423; obj* x_424; obj* x_427; 
lean::dec(x_235);
x_423 = l___private_3255790009__string_mangle__aux___main___closed__1;
x_424 = l___private_1496486805__parse__mangled__string__aux___main___closed__1;
lean::inc(x_424);
lean::inc(x_423);
x_427 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_423, x_424, x_2);
if (lean::obj_tag(x_427) == 0)
{
obj* x_428; obj* x_430; obj* x_433; 
x_428 = lean::cnstr_get(x_427, 1);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_427, 2);
lean::inc(x_430);
lean::dec(x_427);
x_433 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_428);
if (lean::obj_tag(x_433) == 0)
{
obj* x_434; obj* x_436; obj* x_438; obj* x_441; 
x_434 = lean::cnstr_get(x_433, 0);
lean::inc(x_434);
x_436 = lean::cnstr_get(x_433, 1);
lean::inc(x_436);
x_438 = lean::cnstr_get(x_433, 2);
lean::inc(x_438);
lean::dec(x_433);
x_441 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_436);
if (lean::obj_tag(x_441) == 0)
{
obj* x_442; obj* x_444; obj* x_446; obj* x_449; 
x_442 = lean::cnstr_get(x_441, 0);
lean::inc(x_442);
x_444 = lean::cnstr_get(x_441, 1);
lean::inc(x_444);
x_446 = lean::cnstr_get(x_441, 2);
lean::inc(x_446);
lean::dec(x_441);
x_449 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_444);
if (lean::obj_tag(x_449) == 0)
{
obj* x_450; obj* x_452; obj* x_454; obj* x_457; 
x_450 = lean::cnstr_get(x_449, 0);
lean::inc(x_450);
x_452 = lean::cnstr_get(x_449, 1);
lean::inc(x_452);
x_454 = lean::cnstr_get(x_449, 2);
lean::inc(x_454);
lean::dec(x_449);
x_457 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_452);
if (lean::obj_tag(x_457) == 0)
{
obj* x_458; obj* x_460; obj* x_462; obj* x_465; obj* x_466; obj* x_469; obj* x_470; obj* x_473; obj* x_476; obj* x_477; obj* x_480; obj* x_483; obj* x_486; obj* x_487; 
x_458 = lean::cnstr_get(x_457, 0);
lean::inc(x_458);
x_460 = lean::cnstr_get(x_457, 1);
lean::inc(x_460);
x_462 = lean::cnstr_get(x_457, 2);
lean::inc(x_462);
lean::dec(x_457);
x_465 = lean::mk_nat_obj(4096u);
x_466 = lean::nat_mul(x_434, x_465);
lean::dec(x_465);
lean::dec(x_434);
x_469 = lean::mk_nat_obj(256u);
x_470 = lean::nat_mul(x_442, x_469);
lean::dec(x_469);
lean::dec(x_442);
x_473 = lean::nat_add(x_466, x_470);
lean::dec(x_470);
lean::dec(x_466);
x_476 = lean::mk_nat_obj(16u);
x_477 = lean::nat_mul(x_450, x_476);
lean::dec(x_476);
lean::dec(x_450);
x_480 = lean::nat_add(x_473, x_477);
lean::dec(x_477);
lean::dec(x_473);
x_483 = lean::nat_add(x_480, x_458);
lean::dec(x_458);
lean::dec(x_480);
x_486 = lean::mk_nat_obj(55296u);
x_487 = lean::nat_dec_lt(x_483, x_486);
lean::dec(x_486);
if (lean::obj_tag(x_487) == 0)
{
obj* x_490; obj* x_491; 
lean::dec(x_487);
x_490 = lean::mk_nat_obj(57343u);
x_491 = lean::nat_dec_lt(x_490, x_483);
lean::dec(x_490);
if (lean::obj_tag(x_491) == 0)
{
unsigned x_495; obj* x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; 
lean::dec(x_483);
lean::dec(x_491);
x_495 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_497 = lean::string_push(x_1, x_495);
x_498 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_497, x_460);
x_499 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_462, x_498);
x_500 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_454, x_499);
x_501 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_500);
x_502 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_501);
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_502);
x_504 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_503);
x_505 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_504);
x_506 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_505);
x_507 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_506);
x_508 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_507);
return x_508;
}
else
{
obj* x_510; obj* x_511; 
lean::dec(x_491);
x_510 = lean::mk_nat_obj(1114112u);
x_511 = lean::nat_dec_lt(x_483, x_510);
lean::dec(x_510);
if (lean::obj_tag(x_511) == 0)
{
unsigned x_515; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_483);
lean::dec(x_511);
x_515 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_517 = lean::string_push(x_1, x_515);
x_518 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_517, x_460);
x_519 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_462, x_518);
x_520 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_454, x_519);
x_521 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_520);
x_522 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_521);
x_523 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_522);
x_524 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_523);
x_525 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_524);
x_526 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_525);
x_527 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_526);
x_528 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_527);
return x_528;
}
else
{
unsigned x_531; obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; obj* x_542; obj* x_543; obj* x_544; 
lean::dec(x_3);
lean::dec(x_511);
x_531 = lean::unbox_uint32(x_483);
lean::dec(x_483);
x_533 = lean::string_push(x_1, x_531);
x_534 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_533, x_460);
x_535 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_462, x_534);
x_536 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_454, x_535);
x_537 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_536);
x_538 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_537);
x_539 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_538);
x_540 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_539);
x_541 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_540);
x_542 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_541);
x_543 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_542);
x_544 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_543);
return x_544;
}
}
}
else
{
unsigned x_547; obj* x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
lean::dec(x_3);
lean::dec(x_487);
x_547 = lean::unbox_uint32(x_483);
lean::dec(x_483);
x_549 = lean::string_push(x_1, x_547);
x_550 = l___private_1496486805__parse__mangled__string__aux___main(x_7, x_549, x_460);
x_551 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_462, x_550);
x_552 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_454, x_551);
x_553 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_552);
x_554 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_553);
x_555 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_554);
x_556 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_555);
x_557 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_556);
x_558 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_557);
x_559 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_558);
x_560 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_559);
return x_560;
}
}
else
{
obj* x_567; unsigned char x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_442);
lean::dec(x_434);
lean::dec(x_450);
x_567 = lean::cnstr_get(x_457, 0);
lean::inc(x_567);
x_569 = lean::cnstr_get_scalar<unsigned char>(x_457, sizeof(void*)*1);
if (lean::is_shared(x_457)) {
 lean::dec(x_457);
 x_570 = lean::box(0);
} else {
 lean::cnstr_release(x_457, 0);
 x_570 = x_457;
}
if (lean::is_scalar(x_570)) {
 x_571 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_571 = x_570;
}
lean::cnstr_set(x_571, 0, x_567);
lean::cnstr_set_scalar(x_571, sizeof(void*)*1, x_569);
x_572 = x_571;
x_573 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_454, x_572);
x_574 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_573);
x_575 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_574);
x_576 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_575);
x_577 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_576);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_577);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_578);
x_580 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_579);
x_581 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_580);
return x_581;
}
}
else
{
obj* x_587; unsigned char x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_442);
lean::dec(x_434);
x_587 = lean::cnstr_get(x_449, 0);
lean::inc(x_587);
x_589 = lean::cnstr_get_scalar<unsigned char>(x_449, sizeof(void*)*1);
if (lean::is_shared(x_449)) {
 lean::dec(x_449);
 x_590 = lean::box(0);
} else {
 lean::cnstr_release(x_449, 0);
 x_590 = x_449;
}
if (lean::is_scalar(x_590)) {
 x_591 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_591 = x_590;
}
lean::cnstr_set(x_591, 0, x_587);
lean::cnstr_set_scalar(x_591, sizeof(void*)*1, x_589);
x_592 = x_591;
x_593 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_446, x_592);
x_594 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_593);
x_595 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_594);
x_596 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_595);
x_597 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_596);
x_598 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_597);
x_599 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_598);
x_600 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_599);
return x_600;
}
}
else
{
obj* x_605; unsigned char x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_434);
x_605 = lean::cnstr_get(x_441, 0);
lean::inc(x_605);
x_607 = lean::cnstr_get_scalar<unsigned char>(x_441, sizeof(void*)*1);
if (lean::is_shared(x_441)) {
 lean::dec(x_441);
 x_608 = lean::box(0);
} else {
 lean::cnstr_release(x_441, 0);
 x_608 = x_441;
}
if (lean::is_scalar(x_608)) {
 x_609 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_609 = x_608;
}
lean::cnstr_set(x_609, 0, x_605);
lean::cnstr_set_scalar(x_609, sizeof(void*)*1, x_607);
x_610 = x_609;
x_611 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_438, x_610);
x_612 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_611);
x_613 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_612);
x_614 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_613);
x_615 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_614);
x_616 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_615);
x_617 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_616);
return x_617;
}
}
else
{
obj* x_621; unsigned char x_623; obj* x_624; obj* x_625; obj* x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
x_621 = lean::cnstr_get(x_433, 0);
lean::inc(x_621);
x_623 = lean::cnstr_get_scalar<unsigned char>(x_433, sizeof(void*)*1);
if (lean::is_shared(x_433)) {
 lean::dec(x_433);
 x_624 = lean::box(0);
} else {
 lean::cnstr_release(x_433, 0);
 x_624 = x_433;
}
if (lean::is_scalar(x_624)) {
 x_625 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_625 = x_624;
}
lean::cnstr_set(x_625, 0, x_621);
lean::cnstr_set_scalar(x_625, sizeof(void*)*1, x_623);
x_626 = x_625;
x_627 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_430, x_626);
x_628 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_627);
x_629 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_628);
x_630 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_629);
x_631 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_630);
x_632 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_631);
return x_632;
}
}
else
{
obj* x_636; unsigned char x_638; obj* x_639; obj* x_640; obj* x_641; obj* x_642; obj* x_643; obj* x_644; obj* x_645; obj* x_646; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
x_636 = lean::cnstr_get(x_427, 0);
lean::inc(x_636);
x_638 = lean::cnstr_get_scalar<unsigned char>(x_427, sizeof(void*)*1);
if (lean::is_shared(x_427)) {
 lean::dec(x_427);
 x_639 = lean::box(0);
} else {
 lean::cnstr_release(x_427, 0);
 x_639 = x_427;
}
if (lean::is_scalar(x_639)) {
 x_640 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_640 = x_639;
}
lean::cnstr_set(x_640, 0, x_636);
lean::cnstr_set_scalar(x_640, sizeof(void*)*1, x_638);
x_641 = x_640;
x_642 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_236, x_641);
x_643 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_642);
x_644 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_643);
x_645 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_644);
x_646 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_645);
return x_646;
}
}
else
{
obj* x_652; obj* x_653; obj* x_654; obj* x_655; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_236);
x_652 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_122, x_235);
x_653 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_652);
x_654 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_653);
x_655 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_654);
return x_655;
}
}
}
}
}
}
}
}
else
{
obj* x_659; obj* x_661; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_659 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_659);
x_661 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_661, 0, x_1);
lean::cnstr_set(x_661, 1, x_2);
lean::cnstr_set(x_661, 2, x_659);
return x_661;
}
}
}
obj* _init_l___private_1496486805__parse__mangled__string__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_u");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_1496486805__parse__mangled__string__aux___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_x");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_1496486805__parse__mangled__string__aux___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("__");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; 
lean::inc(x_0);
x_4 = l_string_is__empty(x_0);
if (x_4 == 0)
{
obj* x_5; obj* x_7; obj* x_9; 
x_5 = lean::string_length(x_0);
lean::inc(x_0);
x_7 = lean::string_mk_iterator(x_0);
lean::inc(x_2);
x_9 = l___private_580269747__str__aux___main(x_5, x_7, x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_13; obj* x_15; unsigned char x_16; obj* x_17; obj* x_18; 
lean::dec(x_9);
lean::dec(x_0);
x_12 = lean::box(0);
x_13 = l_string_join___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_1);
lean::cnstr_set(x_15, 3, x_12);
x_16 = 0;
x_17 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_16);
x_18 = x_17;
return x_18;
}
else
{
obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_1);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_9, 0);
lean::inc(x_21);
lean::dec(x_9);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_21);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
}
else
{
obj* x_28; obj* x_29; obj* x_32; 
lean::dec(x_1);
lean::dec(x_0);
x_28 = l_string_join___closed__1;
x_29 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_29);
lean::inc(x_28);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_2);
lean::cnstr_set(x_32, 2, x_29);
return x_32;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
x_5 = l_option_get__or__else___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_digit___at___private_1496486805__parse__mangled__string__aux___main___spec__4(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_9);
return x_8;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_21 = x_13;
}
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_23, 0, x_4);
lean::closure_set(x_23, 1, x_19);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
}
else
{
obj* x_26; unsigned char x_28; 
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (x_28 == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_8);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 2);
lean::inc(x_34);
lean::inc(x_4);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_37, 0, x_4);
lean::closure_set(x_37, 1, x_34);
x_38 = lean::cnstr_get(x_26, 3);
lean::inc(x_38);
lean::dec(x_26);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_32);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_38);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_28);
x_43 = x_42;
return x_43;
}
else
{
lean::dec(x_26);
return x_8;
}
}
}
else
{
unsigned x_45; unsigned char x_46; 
x_45 = lean::string_iterator_curr(x_0);
x_46 = l_char_is__digit(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_57; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_53);
lean::inc(x_54);
x_57 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_52, x_54, x_53, x_53, x_0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 2);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_58);
lean::dec(x_60);
lean::dec(x_62);
return x_57;
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
lean::inc(x_54);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_72, 0, x_54);
lean::closure_set(x_72, 1, x_68);
if (lean::is_scalar(x_70)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_70;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
}
else
{
obj* x_75; unsigned char x_77; 
x_75 = lean::cnstr_get(x_57, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_57);
x_79 = lean::cnstr_get(x_75, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_75, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_75, 2);
lean::inc(x_83);
lean::inc(x_54);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_86, 0, x_54);
lean::closure_set(x_86, 1, x_83);
x_87 = lean::cnstr_get(x_75, 3);
lean::inc(x_87);
lean::dec(x_75);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_79);
lean::cnstr_set(x_90, 1, x_81);
lean::cnstr_set(x_90, 2, x_86);
lean::cnstr_set(x_90, 3, x_87);
x_91 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_77);
x_92 = x_91;
return x_92;
}
else
{
lean::dec(x_75);
return x_57;
}
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::string_iterator_next(x_0);
x_95 = lean::box(0);
x_96 = lean::box_uint32(x_45);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set(x_97, 2, x_95);
return x_97;
}
}
}
}
obj* l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; unsigned char x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at___private_1496486805__parse__mangled__string__aux___main___spec__4(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_13 = x_6;
}
x_14 = lean::mk_nat_obj(48u);
x_15 = lean::mk_nat_obj(55296u);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_16);
x_19 = lean::mk_nat_obj(57343u);
x_20 = lean::nat_dec_lt(x_19, x_14);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_25; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_20);
lean::dec(x_14);
x_24 = lean::mk_nat_obj(0u);
x_25 = lean::nat_sub(x_7, x_24);
lean::dec(x_24);
lean::dec(x_7);
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_28);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_9);
lean::cnstr_set(x_30, 2, x_28);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; obj* x_35; 
lean::dec(x_0);
x_33 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_33);
x_35 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_31, x_33);
return x_35;
}
else
{
obj* x_36; unsigned char x_38; 
x_36 = lean::cnstr_get(x_31, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<unsigned char>(x_31, sizeof(void*)*1);
x_1 = x_31;
x_2 = x_36;
x_3 = x_38;
goto lbl_4;
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_20);
x_40 = lean::mk_nat_obj(1114112u);
x_41 = lean::nat_dec_lt(x_14, x_40);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_46; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_14);
lean::dec(x_41);
x_45 = lean::mk_nat_obj(0u);
x_46 = lean::nat_sub(x_7, x_45);
lean::dec(x_45);
lean::dec(x_7);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_49);
if (lean::is_scalar(x_13)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_13;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_9);
lean::cnstr_set(x_51, 2, x_49);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; obj* x_56; 
lean::dec(x_0);
x_54 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_52, x_54);
return x_56;
}
else
{
obj* x_57; unsigned char x_59; 
x_57 = lean::cnstr_get(x_52, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get_scalar<unsigned char>(x_52, sizeof(void*)*1);
x_1 = x_52;
x_2 = x_57;
x_3 = x_59;
goto lbl_4;
}
}
else
{
obj* x_61; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_41);
x_61 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_64);
if (lean::is_scalar(x_13)) {
 x_66 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_66 = x_13;
}
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set(x_66, 1, x_9);
lean::cnstr_set(x_66, 2, x_64);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; 
lean::dec(x_0);
x_69 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_69);
x_71 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_69);
return x_71;
}
else
{
obj* x_72; unsigned char x_74; 
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get_scalar<unsigned char>(x_67, sizeof(void*)*1);
x_1 = x_67;
x_2 = x_72;
x_3 = x_74;
goto lbl_4;
}
}
}
}
else
{
obj* x_76; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_16);
x_76 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
if (lean::is_scalar(x_13)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_13;
}
lean::cnstr_set(x_81, 0, x_76);
lean::cnstr_set(x_81, 1, x_9);
lean::cnstr_set(x_81, 2, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_84; obj* x_86; 
lean::dec(x_0);
x_84 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_84);
x_86 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_82, x_84);
return x_86;
}
else
{
obj* x_87; unsigned char x_89; 
x_87 = lean::cnstr_get(x_82, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get_scalar<unsigned char>(x_82, sizeof(void*)*1);
x_1 = x_82;
x_2 = x_87;
x_3 = x_89;
goto lbl_4;
}
}
}
else
{
obj* x_90; unsigned char x_92; obj* x_93; obj* x_95; obj* x_96; 
x_90 = lean::cnstr_get(x_6, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_93 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_93 = x_6;
}
lean::inc(x_90);
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_90);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_92);
x_96 = x_95;
x_1 = x_96;
x_2 = x_90;
x_3 = x_92;
goto lbl_4;
}
lbl_4:
{
obj* x_97; obj* x_98; unsigned char x_99; 
if (x_3 == 0)
{
obj* x_102; unsigned char x_104; 
lean::dec(x_1);
x_104 = lean::string_iterator_has_next(x_0);
if (x_104 == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_112; 
x_105 = lean::box(0);
x_106 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_107 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_105);
lean::inc(x_107);
lean::inc(x_106);
x_112 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_106, x_107, x_105, x_105, x_0);
x_102 = x_112;
goto lbl_103;
}
else
{
unsigned x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_119; obj* x_120; unsigned char x_121; 
x_113 = lean::string_iterator_curr(x_0);
x_118 = lean::mk_nat_obj(97u);
x_119 = lean::mk_nat_obj(55296u);
x_120 = lean::nat_dec_lt(x_118, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_124; obj* x_125; 
lean::dec(x_120);
x_124 = lean::mk_nat_obj(57343u);
x_125 = lean::nat_dec_lt(x_124, x_118);
lean::dec(x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_118);
lean::dec(x_125);
x_129 = lean::mk_nat_obj(0u);
x_130 = lean::box_uint32(x_113);
x_131 = lean::nat_dec_le(x_129, x_130);
lean::dec(x_130);
lean::dec(x_129);
if (lean::obj_tag(x_131) == 0)
{
obj* x_136; 
lean::dec(x_119);
lean::dec(x_131);
x_136 = lean::box(0);
x_114 = x_136;
goto lbl_115;
}
else
{
unsigned char x_138; 
lean::dec(x_131);
x_138 = 1;
x_121 = x_138;
goto lbl_122;
}
}
else
{
obj* x_140; obj* x_141; 
lean::dec(x_125);
x_140 = lean::mk_nat_obj(1114112u);
x_141 = lean::nat_dec_lt(x_118, x_140);
lean::dec(x_140);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_141);
lean::dec(x_118);
x_145 = lean::mk_nat_obj(0u);
x_146 = lean::box_uint32(x_113);
x_147 = lean::nat_dec_le(x_145, x_146);
lean::dec(x_146);
lean::dec(x_145);
if (lean::obj_tag(x_147) == 0)
{
obj* x_152; 
lean::dec(x_147);
lean::dec(x_119);
x_152 = lean::box(0);
x_114 = x_152;
goto lbl_115;
}
else
{
unsigned char x_154; 
lean::dec(x_147);
x_154 = 1;
x_121 = x_154;
goto lbl_122;
}
}
else
{
obj* x_156; obj* x_157; 
lean::dec(x_141);
x_156 = lean::box_uint32(x_113);
x_157 = lean::nat_dec_le(x_118, x_156);
lean::dec(x_156);
lean::dec(x_118);
if (lean::obj_tag(x_157) == 0)
{
obj* x_162; 
lean::dec(x_157);
lean::dec(x_119);
x_162 = lean::box(0);
x_114 = x_162;
goto lbl_115;
}
else
{
unsigned char x_164; 
lean::dec(x_157);
x_164 = 1;
x_121 = x_164;
goto lbl_122;
}
}
}
}
else
{
obj* x_166; obj* x_167; 
lean::dec(x_120);
x_166 = lean::box_uint32(x_113);
x_167 = lean::nat_dec_le(x_118, x_166);
lean::dec(x_166);
lean::dec(x_118);
if (lean::obj_tag(x_167) == 0)
{
obj* x_172; 
lean::dec(x_167);
lean::dec(x_119);
x_172 = lean::box(0);
x_114 = x_172;
goto lbl_115;
}
else
{
unsigned char x_174; 
lean::dec(x_167);
x_174 = 1;
x_121 = x_174;
goto lbl_122;
}
}
lbl_115:
{
obj* x_176; obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_183; obj* x_187; 
lean::dec(x_114);
x_176 = l_char_quote__core(x_113);
x_177 = l_char_has__repr___closed__1;
lean::inc(x_177);
x_179 = lean::string_append(x_177, x_176);
lean::dec(x_176);
x_181 = lean::string_append(x_179, x_177);
x_182 = lean::box(0);
x_183 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_182);
lean::inc(x_183);
x_187 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_181, x_183, x_182, x_182, x_0);
x_102 = x_187;
goto lbl_103;
}
lbl_117:
{
obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_116);
lean::inc(x_0);
x_190 = lean::string_iterator_next(x_0);
x_191 = lean::box(0);
x_192 = lean::box_uint32(x_113);
x_193 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_190);
lean::cnstr_set(x_193, 2, x_191);
x_102 = x_193;
goto lbl_103;
}
lbl_122:
{
obj* x_194; obj* x_195; 
x_194 = lean::mk_nat_obj(102u);
x_195 = lean::nat_dec_lt(x_194, x_119);
lean::dec(x_119);
if (lean::obj_tag(x_195) == 0)
{
obj* x_198; obj* x_199; 
lean::dec(x_195);
x_198 = lean::mk_nat_obj(57343u);
x_199 = lean::nat_dec_lt(x_198, x_194);
lean::dec(x_198);
if (lean::obj_tag(x_199) == 0)
{
obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_194);
lean::dec(x_199);
x_203 = lean::mk_nat_obj(0u);
x_204 = lean::box_uint32(x_113);
x_205 = lean::nat_dec_le(x_204, x_203);
lean::dec(x_203);
lean::dec(x_204);
if (lean::obj_tag(x_205) == 0)
{
obj* x_209; 
lean::dec(x_205);
x_209 = lean::box(0);
x_114 = x_209;
goto lbl_115;
}
else
{
lean::dec(x_205);
if (x_121 == 0)
{
obj* x_211; 
x_211 = lean::box(0);
x_114 = x_211;
goto lbl_115;
}
else
{
obj* x_212; 
x_212 = lean::box(0);
x_116 = x_212;
goto lbl_117;
}
}
}
else
{
obj* x_214; obj* x_215; 
lean::dec(x_199);
x_214 = lean::mk_nat_obj(1114112u);
x_215 = lean::nat_dec_lt(x_194, x_214);
lean::dec(x_214);
if (lean::obj_tag(x_215) == 0)
{
obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_215);
lean::dec(x_194);
x_219 = lean::mk_nat_obj(0u);
x_220 = lean::box_uint32(x_113);
x_221 = lean::nat_dec_le(x_220, x_219);
lean::dec(x_219);
lean::dec(x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_225; 
lean::dec(x_221);
x_225 = lean::box(0);
x_114 = x_225;
goto lbl_115;
}
else
{
lean::dec(x_221);
if (x_121 == 0)
{
obj* x_227; 
x_227 = lean::box(0);
x_114 = x_227;
goto lbl_115;
}
else
{
obj* x_228; 
x_228 = lean::box(0);
x_116 = x_228;
goto lbl_117;
}
}
}
else
{
obj* x_230; obj* x_231; 
lean::dec(x_215);
x_230 = lean::box_uint32(x_113);
x_231 = lean::nat_dec_le(x_230, x_194);
lean::dec(x_194);
lean::dec(x_230);
if (lean::obj_tag(x_231) == 0)
{
obj* x_235; 
lean::dec(x_231);
x_235 = lean::box(0);
x_114 = x_235;
goto lbl_115;
}
else
{
lean::dec(x_231);
if (x_121 == 0)
{
obj* x_237; 
x_237 = lean::box(0);
x_114 = x_237;
goto lbl_115;
}
else
{
obj* x_238; 
x_238 = lean::box(0);
x_116 = x_238;
goto lbl_117;
}
}
}
}
}
else
{
obj* x_240; obj* x_241; 
lean::dec(x_195);
x_240 = lean::box_uint32(x_113);
x_241 = lean::nat_dec_le(x_240, x_194);
lean::dec(x_194);
lean::dec(x_240);
if (lean::obj_tag(x_241) == 0)
{
obj* x_245; 
lean::dec(x_241);
x_245 = lean::box(0);
x_114 = x_245;
goto lbl_115;
}
else
{
lean::dec(x_241);
if (x_121 == 0)
{
obj* x_247; 
x_247 = lean::box(0);
x_114 = x_247;
goto lbl_115;
}
else
{
obj* x_248; 
x_248 = lean::box(0);
x_116 = x_248;
goto lbl_117;
}
}
}
}
}
lbl_103:
{
obj* x_249; obj* x_251; 
x_249 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_249);
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_102);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_254; obj* x_256; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_251, 2);
lean::inc(x_256);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_258 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 lean::cnstr_release(x_251, 1);
 lean::cnstr_release(x_251, 2);
 x_258 = x_251;
}
x_259 = lean::mk_nat_obj(97u);
x_260 = lean::mk_nat_obj(55296u);
x_261 = lean::nat_dec_lt(x_259, x_260);
lean::dec(x_260);
if (lean::obj_tag(x_261) == 0)
{
obj* x_264; obj* x_265; 
lean::dec(x_261);
x_264 = lean::mk_nat_obj(57343u);
x_265 = lean::nat_dec_lt(x_264, x_259);
lean::dec(x_264);
if (lean::obj_tag(x_265) == 0)
{
obj* x_269; obj* x_270; obj* x_273; obj* x_274; obj* x_278; obj* x_279; 
lean::dec(x_265);
lean::dec(x_259);
x_269 = lean::mk_nat_obj(0u);
x_270 = lean::nat_sub(x_252, x_269);
lean::dec(x_269);
lean::dec(x_252);
x_273 = lean::mk_nat_obj(10u);
x_274 = lean::nat_add(x_273, x_270);
lean::dec(x_270);
lean::dec(x_273);
lean::inc(x_249);
if (lean::is_scalar(x_258)) {
 x_278 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_278 = x_258;
}
lean::cnstr_set(x_278, 0, x_274);
lean::cnstr_set(x_278, 1, x_254);
lean::cnstr_set(x_278, 2, x_249);
x_279 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_278);
if (lean::obj_tag(x_279) == 0)
{
obj* x_281; obj* x_282; obj* x_284; 
lean::dec(x_0);
x_281 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_279);
x_282 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_282);
x_284 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_281, x_282);
return x_284;
}
else
{
obj* x_285; unsigned char x_287; 
x_285 = lean::cnstr_get(x_279, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get_scalar<unsigned char>(x_279, sizeof(void*)*1);
x_97 = x_279;
x_98 = x_285;
x_99 = x_287;
goto lbl_100;
}
}
else
{
obj* x_289; obj* x_290; 
lean::dec(x_265);
x_289 = lean::mk_nat_obj(1114112u);
x_290 = lean::nat_dec_lt(x_259, x_289);
lean::dec(x_289);
if (lean::obj_tag(x_290) == 0)
{
obj* x_294; obj* x_295; obj* x_298; obj* x_299; obj* x_303; obj* x_304; 
lean::dec(x_259);
lean::dec(x_290);
x_294 = lean::mk_nat_obj(0u);
x_295 = lean::nat_sub(x_252, x_294);
lean::dec(x_294);
lean::dec(x_252);
x_298 = lean::mk_nat_obj(10u);
x_299 = lean::nat_add(x_298, x_295);
lean::dec(x_295);
lean::dec(x_298);
lean::inc(x_249);
if (lean::is_scalar(x_258)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_258;
}
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_254);
lean::cnstr_set(x_303, 2, x_249);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_303);
if (lean::obj_tag(x_304) == 0)
{
obj* x_306; obj* x_307; obj* x_309; 
lean::dec(x_0);
x_306 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_304);
x_307 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_307);
x_309 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_306, x_307);
return x_309;
}
else
{
obj* x_310; unsigned char x_312; 
x_310 = lean::cnstr_get(x_304, 0);
lean::inc(x_310);
x_312 = lean::cnstr_get_scalar<unsigned char>(x_304, sizeof(void*)*1);
x_97 = x_304;
x_98 = x_310;
x_99 = x_312;
goto lbl_100;
}
}
else
{
obj* x_314; obj* x_317; obj* x_318; obj* x_322; obj* x_323; 
lean::dec(x_290);
x_314 = lean::nat_sub(x_252, x_259);
lean::dec(x_259);
lean::dec(x_252);
x_317 = lean::mk_nat_obj(10u);
x_318 = lean::nat_add(x_317, x_314);
lean::dec(x_314);
lean::dec(x_317);
lean::inc(x_249);
if (lean::is_scalar(x_258)) {
 x_322 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_322 = x_258;
}
lean::cnstr_set(x_322, 0, x_318);
lean::cnstr_set(x_322, 1, x_254);
lean::cnstr_set(x_322, 2, x_249);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_322);
if (lean::obj_tag(x_323) == 0)
{
obj* x_325; obj* x_326; obj* x_328; 
lean::dec(x_0);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_323);
x_326 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_326);
x_328 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_325, x_326);
return x_328;
}
else
{
obj* x_329; unsigned char x_331; 
x_329 = lean::cnstr_get(x_323, 0);
lean::inc(x_329);
x_331 = lean::cnstr_get_scalar<unsigned char>(x_323, sizeof(void*)*1);
x_97 = x_323;
x_98 = x_329;
x_99 = x_331;
goto lbl_100;
}
}
}
}
else
{
obj* x_333; obj* x_336; obj* x_337; obj* x_341; obj* x_342; 
lean::dec(x_261);
x_333 = lean::nat_sub(x_252, x_259);
lean::dec(x_259);
lean::dec(x_252);
x_336 = lean::mk_nat_obj(10u);
x_337 = lean::nat_add(x_336, x_333);
lean::dec(x_333);
lean::dec(x_336);
lean::inc(x_249);
if (lean::is_scalar(x_258)) {
 x_341 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_341 = x_258;
}
lean::cnstr_set(x_341, 0, x_337);
lean::cnstr_set(x_341, 1, x_254);
lean::cnstr_set(x_341, 2, x_249);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_341);
if (lean::obj_tag(x_342) == 0)
{
obj* x_344; obj* x_345; obj* x_347; 
lean::dec(x_0);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_342);
x_345 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_345);
x_347 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_344, x_345);
return x_347;
}
else
{
obj* x_348; unsigned char x_350; 
x_348 = lean::cnstr_get(x_342, 0);
lean::inc(x_348);
x_350 = lean::cnstr_get_scalar<unsigned char>(x_342, sizeof(void*)*1);
x_97 = x_342;
x_98 = x_348;
x_99 = x_350;
goto lbl_100;
}
}
}
else
{
obj* x_351; unsigned char x_353; obj* x_354; obj* x_356; obj* x_357; 
x_351 = lean::cnstr_get(x_251, 0);
lean::inc(x_351);
x_353 = lean::cnstr_get_scalar<unsigned char>(x_251, sizeof(void*)*1);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_354 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_354 = x_251;
}
lean::inc(x_351);
if (lean::is_scalar(x_354)) {
 x_356 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_356 = x_354;
}
lean::cnstr_set(x_356, 0, x_351);
lean::cnstr_set_scalar(x_356, sizeof(void*)*1, x_353);
x_357 = x_356;
x_97 = x_357;
x_98 = x_351;
x_99 = x_353;
goto lbl_100;
}
}
}
else
{
obj* x_360; obj* x_362; 
lean::dec(x_0);
lean::dec(x_2);
x_360 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_360);
x_362 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_360);
return x_362;
}
lbl_100:
{
if (x_99 == 0)
{
obj* x_364; unsigned char x_366; 
lean::dec(x_97);
x_366 = lean::string_iterator_has_next(x_0);
if (x_366 == 0)
{
obj* x_367; obj* x_368; obj* x_369; obj* x_373; 
x_367 = lean::box(0);
x_368 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_369 = l_mjoin___rarg___closed__1;
lean::inc(x_367);
lean::inc(x_369);
lean::inc(x_368);
x_373 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_368, x_369, x_367, x_367, x_0);
x_364 = x_373;
goto lbl_365;
}
else
{
unsigned x_374; obj* x_375; obj* x_377; obj* x_379; obj* x_380; obj* x_381; unsigned char x_382; 
x_374 = lean::string_iterator_curr(x_0);
x_379 = lean::mk_nat_obj(65u);
x_380 = lean::mk_nat_obj(55296u);
x_381 = lean::nat_dec_lt(x_379, x_380);
if (lean::obj_tag(x_381) == 0)
{
obj* x_385; obj* x_386; 
lean::dec(x_381);
x_385 = lean::mk_nat_obj(57343u);
x_386 = lean::nat_dec_lt(x_385, x_379);
lean::dec(x_385);
if (lean::obj_tag(x_386) == 0)
{
obj* x_390; obj* x_391; obj* x_392; 
lean::dec(x_386);
lean::dec(x_379);
x_390 = lean::mk_nat_obj(0u);
x_391 = lean::box_uint32(x_374);
x_392 = lean::nat_dec_le(x_390, x_391);
lean::dec(x_391);
lean::dec(x_390);
if (lean::obj_tag(x_392) == 0)
{
obj* x_397; 
lean::dec(x_392);
lean::dec(x_380);
x_397 = lean::box(0);
x_375 = x_397;
goto lbl_376;
}
else
{
unsigned char x_399; 
lean::dec(x_392);
x_399 = 1;
x_382 = x_399;
goto lbl_383;
}
}
else
{
obj* x_401; obj* x_402; 
lean::dec(x_386);
x_401 = lean::mk_nat_obj(1114112u);
x_402 = lean::nat_dec_lt(x_379, x_401);
lean::dec(x_401);
if (lean::obj_tag(x_402) == 0)
{
obj* x_406; obj* x_407; obj* x_408; 
lean::dec(x_379);
lean::dec(x_402);
x_406 = lean::mk_nat_obj(0u);
x_407 = lean::box_uint32(x_374);
x_408 = lean::nat_dec_le(x_406, x_407);
lean::dec(x_407);
lean::dec(x_406);
if (lean::obj_tag(x_408) == 0)
{
obj* x_413; 
lean::dec(x_380);
lean::dec(x_408);
x_413 = lean::box(0);
x_375 = x_413;
goto lbl_376;
}
else
{
unsigned char x_415; 
lean::dec(x_408);
x_415 = 1;
x_382 = x_415;
goto lbl_383;
}
}
else
{
obj* x_417; obj* x_418; 
lean::dec(x_402);
x_417 = lean::box_uint32(x_374);
x_418 = lean::nat_dec_le(x_379, x_417);
lean::dec(x_417);
lean::dec(x_379);
if (lean::obj_tag(x_418) == 0)
{
obj* x_423; 
lean::dec(x_380);
lean::dec(x_418);
x_423 = lean::box(0);
x_375 = x_423;
goto lbl_376;
}
else
{
unsigned char x_425; 
lean::dec(x_418);
x_425 = 1;
x_382 = x_425;
goto lbl_383;
}
}
}
}
else
{
obj* x_427; obj* x_428; 
lean::dec(x_381);
x_427 = lean::box_uint32(x_374);
x_428 = lean::nat_dec_le(x_379, x_427);
lean::dec(x_427);
lean::dec(x_379);
if (lean::obj_tag(x_428) == 0)
{
obj* x_433; 
lean::dec(x_380);
lean::dec(x_428);
x_433 = lean::box(0);
x_375 = x_433;
goto lbl_376;
}
else
{
unsigned char x_435; 
lean::dec(x_428);
x_435 = 1;
x_382 = x_435;
goto lbl_383;
}
}
lbl_376:
{
obj* x_437; obj* x_438; obj* x_440; obj* x_442; obj* x_443; obj* x_444; obj* x_447; 
lean::dec(x_375);
x_437 = l_char_quote__core(x_374);
x_438 = l_char_has__repr___closed__1;
lean::inc(x_438);
x_440 = lean::string_append(x_438, x_437);
lean::dec(x_437);
x_442 = lean::string_append(x_440, x_438);
x_443 = lean::box(0);
x_444 = l_mjoin___rarg___closed__1;
lean::inc(x_443);
lean::inc(x_444);
x_447 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_442, x_444, x_443, x_443, x_0);
x_364 = x_447;
goto lbl_365;
}
lbl_378:
{
obj* x_449; obj* x_450; obj* x_451; obj* x_452; 
lean::dec(x_377);
x_449 = lean::string_iterator_next(x_0);
x_450 = lean::box(0);
x_451 = lean::box_uint32(x_374);
x_452 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_449);
lean::cnstr_set(x_452, 2, x_450);
x_364 = x_452;
goto lbl_365;
}
lbl_383:
{
obj* x_453; obj* x_454; 
x_453 = lean::mk_nat_obj(70u);
x_454 = lean::nat_dec_lt(x_453, x_380);
lean::dec(x_380);
if (lean::obj_tag(x_454) == 0)
{
obj* x_457; obj* x_458; 
lean::dec(x_454);
x_457 = lean::mk_nat_obj(57343u);
x_458 = lean::nat_dec_lt(x_457, x_453);
lean::dec(x_457);
if (lean::obj_tag(x_458) == 0)
{
obj* x_462; obj* x_463; obj* x_464; 
lean::dec(x_453);
lean::dec(x_458);
x_462 = lean::mk_nat_obj(0u);
x_463 = lean::box_uint32(x_374);
x_464 = lean::nat_dec_le(x_463, x_462);
lean::dec(x_462);
lean::dec(x_463);
if (lean::obj_tag(x_464) == 0)
{
obj* x_468; 
lean::dec(x_464);
x_468 = lean::box(0);
x_375 = x_468;
goto lbl_376;
}
else
{
lean::dec(x_464);
if (x_382 == 0)
{
obj* x_470; 
x_470 = lean::box(0);
x_375 = x_470;
goto lbl_376;
}
else
{
obj* x_471; 
x_471 = lean::box(0);
x_377 = x_471;
goto lbl_378;
}
}
}
else
{
obj* x_473; obj* x_474; 
lean::dec(x_458);
x_473 = lean::mk_nat_obj(1114112u);
x_474 = lean::nat_dec_lt(x_453, x_473);
lean::dec(x_473);
if (lean::obj_tag(x_474) == 0)
{
obj* x_478; obj* x_479; obj* x_480; 
lean::dec(x_453);
lean::dec(x_474);
x_478 = lean::mk_nat_obj(0u);
x_479 = lean::box_uint32(x_374);
x_480 = lean::nat_dec_le(x_479, x_478);
lean::dec(x_478);
lean::dec(x_479);
if (lean::obj_tag(x_480) == 0)
{
obj* x_484; 
lean::dec(x_480);
x_484 = lean::box(0);
x_375 = x_484;
goto lbl_376;
}
else
{
lean::dec(x_480);
if (x_382 == 0)
{
obj* x_486; 
x_486 = lean::box(0);
x_375 = x_486;
goto lbl_376;
}
else
{
obj* x_487; 
x_487 = lean::box(0);
x_377 = x_487;
goto lbl_378;
}
}
}
else
{
obj* x_489; obj* x_490; 
lean::dec(x_474);
x_489 = lean::box_uint32(x_374);
x_490 = lean::nat_dec_le(x_489, x_453);
lean::dec(x_453);
lean::dec(x_489);
if (lean::obj_tag(x_490) == 0)
{
obj* x_494; 
lean::dec(x_490);
x_494 = lean::box(0);
x_375 = x_494;
goto lbl_376;
}
else
{
lean::dec(x_490);
if (x_382 == 0)
{
obj* x_496; 
x_496 = lean::box(0);
x_375 = x_496;
goto lbl_376;
}
else
{
obj* x_497; 
x_497 = lean::box(0);
x_377 = x_497;
goto lbl_378;
}
}
}
}
}
else
{
obj* x_499; obj* x_500; 
lean::dec(x_454);
x_499 = lean::box_uint32(x_374);
x_500 = lean::nat_dec_le(x_499, x_453);
lean::dec(x_453);
lean::dec(x_499);
if (lean::obj_tag(x_500) == 0)
{
obj* x_504; 
lean::dec(x_500);
x_504 = lean::box(0);
x_375 = x_504;
goto lbl_376;
}
else
{
lean::dec(x_500);
if (x_382 == 0)
{
obj* x_506; 
x_506 = lean::box(0);
x_375 = x_506;
goto lbl_376;
}
else
{
obj* x_507; 
x_507 = lean::box(0);
x_377 = x_507;
goto lbl_378;
}
}
}
}
}
lbl_365:
{
obj* x_508; obj* x_510; 
x_508 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_508);
x_510 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_508, x_364);
if (lean::obj_tag(x_510) == 0)
{
obj* x_511; obj* x_513; obj* x_515; obj* x_517; obj* x_518; obj* x_519; obj* x_520; 
x_511 = lean::cnstr_get(x_510, 0);
lean::inc(x_511);
x_513 = lean::cnstr_get(x_510, 1);
lean::inc(x_513);
x_515 = lean::cnstr_get(x_510, 2);
lean::inc(x_515);
if (lean::is_shared(x_510)) {
 lean::dec(x_510);
 x_517 = lean::box(0);
} else {
 lean::cnstr_release(x_510, 0);
 lean::cnstr_release(x_510, 1);
 lean::cnstr_release(x_510, 2);
 x_517 = x_510;
}
x_518 = lean::mk_nat_obj(65u);
x_519 = lean::mk_nat_obj(55296u);
x_520 = lean::nat_dec_lt(x_518, x_519);
lean::dec(x_519);
if (lean::obj_tag(x_520) == 0)
{
obj* x_523; obj* x_524; 
lean::dec(x_520);
x_523 = lean::mk_nat_obj(57343u);
x_524 = lean::nat_dec_lt(x_523, x_518);
lean::dec(x_523);
if (lean::obj_tag(x_524) == 0)
{
obj* x_528; obj* x_529; obj* x_532; obj* x_533; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; obj* x_543; 
lean::dec(x_524);
lean::dec(x_518);
x_528 = lean::mk_nat_obj(0u);
x_529 = lean::nat_sub(x_511, x_528);
lean::dec(x_528);
lean::dec(x_511);
x_532 = lean::mk_nat_obj(10u);
x_533 = lean::nat_add(x_532, x_529);
lean::dec(x_529);
lean::dec(x_532);
lean::inc(x_508);
if (lean::is_scalar(x_517)) {
 x_537 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_537 = x_517;
}
lean::cnstr_set(x_537, 0, x_533);
lean::cnstr_set(x_537, 1, x_513);
lean::cnstr_set(x_537, 2, x_508);
x_538 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_515, x_537);
x_539 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_98, x_538);
x_540 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_539);
x_541 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_541);
x_543 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_540, x_541);
return x_543;
}
else
{
obj* x_545; obj* x_546; 
lean::dec(x_524);
x_545 = lean::mk_nat_obj(1114112u);
x_546 = lean::nat_dec_lt(x_518, x_545);
lean::dec(x_545);
if (lean::obj_tag(x_546) == 0)
{
obj* x_550; obj* x_551; obj* x_554; obj* x_555; obj* x_559; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_565; 
lean::dec(x_546);
lean::dec(x_518);
x_550 = lean::mk_nat_obj(0u);
x_551 = lean::nat_sub(x_511, x_550);
lean::dec(x_550);
lean::dec(x_511);
x_554 = lean::mk_nat_obj(10u);
x_555 = lean::nat_add(x_554, x_551);
lean::dec(x_551);
lean::dec(x_554);
lean::inc(x_508);
if (lean::is_scalar(x_517)) {
 x_559 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_559 = x_517;
}
lean::cnstr_set(x_559, 0, x_555);
lean::cnstr_set(x_559, 1, x_513);
lean::cnstr_set(x_559, 2, x_508);
x_560 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_515, x_559);
x_561 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_98, x_560);
x_562 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_561);
x_563 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_563);
x_565 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_562, x_563);
return x_565;
}
else
{
obj* x_567; obj* x_570; obj* x_571; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_581; 
lean::dec(x_546);
x_567 = lean::nat_sub(x_511, x_518);
lean::dec(x_518);
lean::dec(x_511);
x_570 = lean::mk_nat_obj(10u);
x_571 = lean::nat_add(x_570, x_567);
lean::dec(x_567);
lean::dec(x_570);
lean::inc(x_508);
if (lean::is_scalar(x_517)) {
 x_575 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_575 = x_517;
}
lean::cnstr_set(x_575, 0, x_571);
lean::cnstr_set(x_575, 1, x_513);
lean::cnstr_set(x_575, 2, x_508);
x_576 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_515, x_575);
x_577 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_98, x_576);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_577);
x_579 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_579);
x_581 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_578, x_579);
return x_581;
}
}
}
else
{
obj* x_583; obj* x_586; obj* x_587; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_597; 
lean::dec(x_520);
x_583 = lean::nat_sub(x_511, x_518);
lean::dec(x_518);
lean::dec(x_511);
x_586 = lean::mk_nat_obj(10u);
x_587 = lean::nat_add(x_586, x_583);
lean::dec(x_583);
lean::dec(x_586);
lean::inc(x_508);
if (lean::is_scalar(x_517)) {
 x_591 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_591 = x_517;
}
lean::cnstr_set(x_591, 0, x_587);
lean::cnstr_set(x_591, 1, x_513);
lean::cnstr_set(x_591, 2, x_508);
x_592 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_515, x_591);
x_593 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_98, x_592);
x_594 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_593);
x_595 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_595);
x_597 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_594, x_595);
return x_597;
}
}
else
{
obj* x_598; unsigned char x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; obj* x_606; obj* x_608; 
x_598 = lean::cnstr_get(x_510, 0);
lean::inc(x_598);
x_600 = lean::cnstr_get_scalar<unsigned char>(x_510, sizeof(void*)*1);
if (lean::is_shared(x_510)) {
 lean::dec(x_510);
 x_601 = lean::box(0);
} else {
 lean::cnstr_release(x_510, 0);
 x_601 = x_510;
}
if (lean::is_scalar(x_601)) {
 x_602 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_602 = x_601;
}
lean::cnstr_set(x_602, 0, x_598);
lean::cnstr_set_scalar(x_602, sizeof(void*)*1, x_600);
x_603 = x_602;
x_604 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_98, x_603);
x_605 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_604);
x_606 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_606);
x_608 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_605, x_606);
return x_608;
}
}
}
else
{
obj* x_611; obj* x_612; obj* x_614; 
lean::dec(x_0);
lean::dec(x_98);
x_611 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_97);
x_612 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_612);
x_614 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_611, x_612);
return x_614;
}
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_alpha___at___private_1496486805__parse__mangled__string__aux___main___spec__5(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_9);
return x_8;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_21 = x_13;
}
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_23, 0, x_4);
lean::closure_set(x_23, 1, x_19);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
}
else
{
obj* x_26; unsigned char x_28; 
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (x_28 == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_8);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 2);
lean::inc(x_34);
lean::inc(x_4);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_37, 0, x_4);
lean::closure_set(x_37, 1, x_34);
x_38 = lean::cnstr_get(x_26, 3);
lean::inc(x_38);
lean::dec(x_26);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_32);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_38);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_28);
x_43 = x_42;
return x_43;
}
else
{
lean::dec(x_26);
return x_8;
}
}
}
else
{
unsigned x_45; unsigned char x_46; 
x_45 = lean::string_iterator_curr(x_0);
x_46 = l_char_is__alpha(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_57; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_53);
lean::inc(x_54);
x_57 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_52, x_54, x_53, x_53, x_0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 2);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_58);
lean::dec(x_60);
lean::dec(x_62);
return x_57;
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
lean::inc(x_54);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_72, 0, x_54);
lean::closure_set(x_72, 1, x_68);
if (lean::is_scalar(x_70)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_70;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
}
else
{
obj* x_75; unsigned char x_77; 
x_75 = lean::cnstr_get(x_57, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_57);
x_79 = lean::cnstr_get(x_75, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_75, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_75, 2);
lean::inc(x_83);
lean::inc(x_54);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_86, 0, x_54);
lean::closure_set(x_86, 1, x_83);
x_87 = lean::cnstr_get(x_75, 3);
lean::inc(x_87);
lean::dec(x_75);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_79);
lean::cnstr_set(x_90, 1, x_81);
lean::cnstr_set(x_90, 2, x_86);
lean::cnstr_set(x_90, 3, x_87);
x_91 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_77);
x_92 = x_91;
return x_92;
}
else
{
lean::dec(x_75);
return x_57;
}
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::string_iterator_next(x_0);
x_95 = lean::box(0);
x_96 = lean::box_uint32(x_45);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set(x_97, 2, x_95);
return x_97;
}
}
}
}
obj* l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; 
lean::dec(x_3);
x_7 = lean::string_iterator_curr(x_0);
x_8 = l_char_quote__core(x_7);
x_9 = l_char_has__repr___closed__1;
lean::inc(x_9);
x_11 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_13 = lean::string_append(x_11, x_9);
x_14 = lean::box(0);
x_15 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
lean::inc(x_14);
lean::inc(x_15);
x_18 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_13, x_15, x_14, x_14, x_0);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_23; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 2);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
lean::dec(x_23);
lean::dec(x_19);
lean::dec(x_21);
return x_18;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_18);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
}
x_32 = l_mjoin___rarg___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_29);
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_19);
lean::cnstr_set(x_36, 1, x_21);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
}
else
{
obj* x_37; unsigned char x_39; 
x_37 = lean::cnstr_get(x_18, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<unsigned char>(x_18, sizeof(void*)*1);
if (x_39 == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_18);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
x_47 = l_mjoin___rarg___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_45);
x_50 = lean::cnstr_get(x_37, 3);
lean::inc(x_50);
lean::dec(x_37);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_41);
lean::cnstr_set(x_53, 1, x_43);
lean::cnstr_set(x_53, 2, x_49);
lean::cnstr_set(x_53, 3, x_50);
x_54 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_39);
x_55 = x_54;
return x_55;
}
else
{
lean::dec(x_37);
return x_18;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_3);
x_58 = lean::box(0);
x_59 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_0);
lean::cnstr_set(x_61, 2, x_59);
return x_61;
}
}
}
obj* _init_l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l___private_1496486805__parse__mangled__string__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_1496486805__parse__mangled__string__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_3162311557__parse__mangled__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = l___private_1496486805__parse__mangled__string__aux___main(x_1, x_2, x_0);
x_5 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_5);
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_4);
return x_7;
}
}
obj* l_lean_string_demangle(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; 
x_1 = l_lean_string_demangle___closed__1;
x_2 = l_string_join___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_1, x_0, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; 
lean::dec(x_5);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* _init_l_lean_string_demangle___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3162311557__parse__mangled__string), 1, 0);
return x_0;
}
}
obj* l___private_1205956357__name_mangle__aux___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_1);
return x_0;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l___private_1205956357__name_mangle__aux___main(x_0, x_3);
x_9 = l_lean_string_mangle(x_5);
x_10 = l___private_1205956357__name_mangle__aux___main___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::string_length(x_9);
x_13 = l_nat_repr(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
x_16 = l___private_1205956357__name_mangle__aux___main___closed__2;
x_17 = lean::string_append(x_14, x_16);
x_18 = lean::string_append(x_17, x_9);
lean::dec(x_9);
return x_18;
}
default:
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_1, 1);
lean::inc(x_22);
lean::dec(x_1);
x_25 = l___private_1205956357__name_mangle__aux___main(x_0, x_20);
x_26 = l___private_1205956357__name_mangle__aux___main___closed__2;
x_27 = lean::string_append(x_25, x_26);
x_28 = l_nat_repr(x_22);
x_29 = lean::string_append(x_27, x_28);
lean::dec(x_28);
x_31 = lean::string_append(x_29, x_26);
return x_31;
}
}
}
}
obj* _init_l___private_1205956357__name_mangle__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_s");
return x_0;
}
}
obj* _init_l___private_1205956357__name_mangle__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_");
return x_0;
}
}
obj* l___private_1205956357__name_mangle__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_1205956357__name_mangle__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_mangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_1205956357__name_mangle__aux___main(x_1, x_0);
return x_2;
}
}
obj* l___private_4217055689__parse__mangled__name__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_15; unsigned x_16; 
lean::dec(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(95u);
x_11 = lean::mk_nat_obj(55296u);
x_12 = lean::nat_dec_lt(x_10, x_11);
lean::dec(x_11);
lean::inc(x_2);
x_15 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::mk_nat_obj(57343u);
x_19 = lean::nat_dec_lt(x_18, x_10);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
unsigned x_22; 
lean::dec(x_19);
x_22 = lean::unbox_uint32(x_3);
x_16 = x_22;
goto lbl_17;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_19);
x_24 = lean::mk_nat_obj(1114112u);
x_25 = lean::nat_dec_lt(x_10, x_24);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
unsigned x_28; 
lean::dec(x_25);
x_28 = lean::unbox_uint32(x_3);
x_16 = x_28;
goto lbl_17;
}
else
{
unsigned x_30; 
lean::dec(x_25);
x_30 = lean::unbox_uint32(x_10);
x_16 = x_30;
goto lbl_17;
}
}
}
else
{
unsigned x_31; 
x_31 = lean::unbox_uint32(x_10);
x_16 = x_31;
goto lbl_17;
}
lbl_17:
{
obj* x_32; 
if (lean::obj_tag(x_15) == 0)
{
obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_15, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_15, 2);
lean::inc(x_36);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_38 = x_15;
}
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
lean::inc(x_1);
if (lean::is_scalar(x_38)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_38;
}
lean::cnstr_set(x_42, 0, x_1);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_39);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_42);
x_32 = x_43;
goto lbl_33;
}
else
{
obj* x_44; unsigned char x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_15, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<unsigned char>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_47 = x_15;
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
x_32 = x_49;
goto lbl_33;
}
lbl_33:
{
if (lean::obj_tag(x_32) == 0)
{
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
return x_32;
}
else
{
obj* x_56; unsigned char x_58; obj* x_59; obj* x_60; unsigned char x_61; 
x_56 = lean::cnstr_get(x_32, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<unsigned char>(x_32, sizeof(void*)*1);
if (x_58 == 0)
{
obj* x_64; obj* x_65; obj* x_69; 
lean::dec(x_32);
x_64 = l___private_1205956357__name_mangle__aux___main___closed__1;
x_65 = l___private_4217055689__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_65);
lean::inc(x_64);
x_69 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_64, x_65, x_2);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; 
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 2);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 lean::cnstr_release(x_69, 2);
 x_74 = x_69;
}
x_75 = l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; unsigned x_83; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
if (lean::obj_tag(x_12) == 0)
{
obj* x_86; obj* x_87; 
lean::dec(x_12);
x_86 = lean::mk_nat_obj(57343u);
x_87 = lean::nat_dec_lt(x_86, x_10);
lean::dec(x_86);
if (lean::obj_tag(x_87) == 0)
{
unsigned x_91; 
lean::dec(x_10);
lean::dec(x_87);
x_91 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_83 = x_91;
goto lbl_84;
}
else
{
obj* x_94; obj* x_95; 
lean::dec(x_87);
x_94 = lean::mk_nat_obj(1114112u);
x_95 = lean::nat_dec_lt(x_10, x_94);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
unsigned x_99; 
lean::dec(x_10);
lean::dec(x_95);
x_99 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_83 = x_99;
goto lbl_84;
}
else
{
unsigned x_103; 
lean::dec(x_3);
lean::dec(x_95);
x_103 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_83 = x_103;
goto lbl_84;
}
}
}
else
{
unsigned x_107; 
lean::dec(x_12);
lean::dec(x_3);
x_107 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_83 = x_107;
goto lbl_84;
}
lbl_84:
{
obj* x_109; 
x_109 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_83, x_78);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_115; 
x_110 = lean::cnstr_get(x_109, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 2);
lean::inc(x_112);
lean::dec(x_109);
x_115 = l_lean_parser_monad__parsec_take___at___private_4217055689__parse__mangled__name__aux___main___spec__18(x_76, x_110);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_118; obj* x_120; obj* x_123; obj* x_124; obj* x_126; obj* x_127; 
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 2);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_lean_string_demangle(x_116);
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_124);
if (lean::is_scalar(x_74)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_74;
}
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_118);
lean::cnstr_set(x_126, 2, x_124);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_120, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; obj* x_130; obj* x_132; 
x_128 = lean::cnstr_get(x_127, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_127, 1);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_127, 2);
lean::inc(x_132);
lean::dec(x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_128);
x_136 = l_match__failed___at___private_4217055689__parse__mangled__name__aux___main___spec__19(x_130);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_132, x_136);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_137);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_144; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_144 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_140);
return x_144;
}
else
{
obj* x_145; unsigned char x_147; 
x_145 = lean::cnstr_get(x_140, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<unsigned char>(x_140, sizeof(void*)*1);
x_59 = x_140;
x_60 = x_145;
x_61 = x_147;
goto lbl_62;
}
}
else
{
obj* x_148; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_148 = lean::cnstr_get(x_128, 0);
lean::inc(x_148);
lean::dec(x_128);
lean::inc(x_1);
x_152 = lean::name_mk_string(x_1, x_148);
lean::inc(x_7);
x_154 = l___private_4217055689__parse__mangled__name__aux___main(x_7, x_152, x_130);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_132, x_154);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_156);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_157);
if (lean::obj_tag(x_158) == 0)
{
obj* x_162; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_162 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_158);
return x_162;
}
else
{
obj* x_163; unsigned char x_165; 
x_163 = lean::cnstr_get(x_158, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get_scalar<unsigned char>(x_158, sizeof(void*)*1);
x_59 = x_158;
x_60 = x_163;
x_61 = x_165;
goto lbl_62;
}
}
}
else
{
obj* x_166; unsigned char x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
x_166 = lean::cnstr_get(x_127, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<unsigned char>(x_127, sizeof(void*)*1);
if (lean::is_shared(x_127)) {
 lean::dec(x_127);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_127, 0);
 x_169 = x_127;
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_168);
x_171 = x_170;
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_172);
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_173);
if (lean::obj_tag(x_174) == 0)
{
obj* x_178; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_178 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_174);
return x_178;
}
else
{
obj* x_179; unsigned char x_181; 
x_179 = lean::cnstr_get(x_174, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get_scalar<unsigned char>(x_174, sizeof(void*)*1);
x_59 = x_174;
x_60 = x_179;
x_61 = x_181;
goto lbl_62;
}
}
}
else
{
obj* x_183; unsigned char x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
lean::dec(x_74);
x_183 = lean::cnstr_get(x_115, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get_scalar<unsigned char>(x_115, sizeof(void*)*1);
if (lean::is_shared(x_115)) {
 lean::dec(x_115);
 x_186 = lean::box(0);
} else {
 lean::cnstr_release(x_115, 0);
 x_186 = x_115;
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_183);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_185);
x_188 = x_187;
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_188);
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_189);
x_191 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_195; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_195 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_191);
return x_195;
}
else
{
obj* x_196; unsigned char x_198; 
x_196 = lean::cnstr_get(x_191, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get_scalar<unsigned char>(x_191, sizeof(void*)*1);
x_59 = x_191;
x_60 = x_196;
x_61 = x_198;
goto lbl_62;
}
}
}
else
{
obj* x_201; unsigned char x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_74);
lean::dec(x_76);
x_201 = lean::cnstr_get(x_109, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get_scalar<unsigned char>(x_109, sizeof(void*)*1);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_204 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_204 = x_109;
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_201);
lean::cnstr_set_scalar(x_205, sizeof(void*)*1, x_203);
x_206 = x_205;
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_206);
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_207);
if (lean::obj_tag(x_208) == 0)
{
obj* x_212; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_212 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_208);
return x_212;
}
else
{
obj* x_213; unsigned char x_215; 
x_213 = lean::cnstr_get(x_208, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get_scalar<unsigned char>(x_208, sizeof(void*)*1);
x_59 = x_208;
x_60 = x_213;
x_61 = x_215;
goto lbl_62;
}
}
}
}
else
{
obj* x_220; unsigned char x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_74);
x_220 = lean::cnstr_get(x_75, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get_scalar<unsigned char>(x_75, sizeof(void*)*1);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_223 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_223 = x_75;
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_220);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_222);
x_225 = x_224;
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_225);
if (lean::obj_tag(x_226) == 0)
{
obj* x_230; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_230 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_226);
return x_230;
}
else
{
obj* x_231; unsigned char x_233; 
x_231 = lean::cnstr_get(x_226, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<unsigned char>(x_226, sizeof(void*)*1);
x_59 = x_226;
x_60 = x_231;
x_61 = x_233;
goto lbl_62;
}
}
}
else
{
obj* x_237; unsigned char x_239; obj* x_240; obj* x_242; obj* x_243; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_3);
x_237 = lean::cnstr_get(x_69, 0);
lean::inc(x_237);
x_239 = lean::cnstr_get_scalar<unsigned char>(x_69, sizeof(void*)*1);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_240 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_240 = x_69;
}
lean::inc(x_237);
if (lean::is_scalar(x_240)) {
 x_242 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_242 = x_240;
}
lean::cnstr_set(x_242, 0, x_237);
lean::cnstr_set_scalar(x_242, sizeof(void*)*1, x_239);
x_243 = x_242;
x_59 = x_243;
x_60 = x_237;
x_61 = x_239;
goto lbl_62;
}
}
else
{
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_56);
return x_32;
}
lbl_62:
{
if (x_61 == 0)
{
obj* x_252; 
lean::dec(x_59);
x_252 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_16, x_2);
if (lean::obj_tag(x_252) == 0)
{
obj* x_253; obj* x_255; obj* x_258; 
x_253 = lean::cnstr_get(x_252, 1);
lean::inc(x_253);
x_255 = lean::cnstr_get(x_252, 2);
lean::inc(x_255);
lean::dec(x_252);
x_258 = l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(x_253);
if (lean::obj_tag(x_258) == 0)
{
obj* x_259; obj* x_261; obj* x_263; obj* x_266; 
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_258, 2);
lean::inc(x_263);
lean::dec(x_258);
x_266 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_16, x_261);
if (lean::obj_tag(x_266) == 0)
{
obj* x_267; obj* x_269; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
x_267 = lean::cnstr_get(x_266, 1);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 2);
lean::inc(x_269);
lean::dec(x_266);
x_272 = lean::name_mk_numeral(x_1, x_259);
x_273 = l___private_4217055689__parse__mangled__name__aux___main(x_7, x_272, x_267);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_273);
x_275 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_263, x_274);
x_276 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_255, x_275);
x_277 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_60, x_276);
x_278 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_277);
return x_278;
}
else
{
obj* x_282; unsigned char x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; 
lean::dec(x_259);
lean::dec(x_1);
lean::dec(x_7);
x_282 = lean::cnstr_get(x_266, 0);
lean::inc(x_282);
x_284 = lean::cnstr_get_scalar<unsigned char>(x_266, sizeof(void*)*1);
if (lean::is_shared(x_266)) {
 lean::dec(x_266);
 x_285 = lean::box(0);
} else {
 lean::cnstr_release(x_266, 0);
 x_285 = x_266;
}
if (lean::is_scalar(x_285)) {
 x_286 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_286 = x_285;
}
lean::cnstr_set(x_286, 0, x_282);
lean::cnstr_set_scalar(x_286, sizeof(void*)*1, x_284);
x_287 = x_286;
x_288 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_263, x_287);
x_289 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_255, x_288);
x_290 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_60, x_289);
x_291 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_290);
return x_291;
}
}
else
{
obj* x_294; unsigned char x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_1);
lean::dec(x_7);
x_294 = lean::cnstr_get(x_258, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get_scalar<unsigned char>(x_258, sizeof(void*)*1);
if (lean::is_shared(x_258)) {
 lean::dec(x_258);
 x_297 = lean::box(0);
} else {
 lean::cnstr_release(x_258, 0);
 x_297 = x_258;
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_294);
lean::cnstr_set_scalar(x_298, sizeof(void*)*1, x_296);
x_299 = x_298;
x_300 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_255, x_299);
x_301 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_60, x_300);
x_302 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_301);
return x_302;
}
}
else
{
obj* x_305; unsigned char x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_1);
lean::dec(x_7);
x_305 = lean::cnstr_get(x_252, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get_scalar<unsigned char>(x_252, sizeof(void*)*1);
if (lean::is_shared(x_252)) {
 lean::dec(x_252);
 x_308 = lean::box(0);
} else {
 lean::cnstr_release(x_252, 0);
 x_308 = x_252;
}
if (lean::is_scalar(x_308)) {
 x_309 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_309 = x_308;
}
lean::cnstr_set(x_309, 0, x_305);
lean::cnstr_set_scalar(x_309, sizeof(void*)*1, x_307);
x_310 = x_309;
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_60, x_310);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_311);
return x_312;
}
}
else
{
obj* x_317; 
lean::dec(x_60);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_317 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_56, x_59);
return x_317;
}
}
}
}
}
}
else
{
obj* x_321; obj* x_323; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_321 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_321);
x_323 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_323, 0, x_1);
lean::cnstr_set(x_323, 1, x_2);
lean::cnstr_set(x_323, 2, x_321);
return x_323;
}
}
}
obj* _init_l___private_4217055689__parse__mangled__name__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_s");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(unsigned x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
x_2 = lean::string_iterator_has_next(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_10);
return x_9;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_9);
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_22 = x_14;
}
lean::inc(x_5);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_24, 0, x_5);
lean::closure_set(x_24, 1, x_20);
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
}
else
{
obj* x_27; unsigned char x_29; 
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
if (x_29 == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_27, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 2);
lean::inc(x_35);
lean::inc(x_5);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_38, 0, x_5);
lean::closure_set(x_38, 1, x_35);
x_39 = lean::cnstr_get(x_27, 3);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_31);
lean::cnstr_set(x_42, 1, x_33);
lean::cnstr_set(x_42, 2, x_38);
lean::cnstr_set(x_42, 3, x_39);
x_43 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_29);
x_44 = x_43;
return x_44;
}
else
{
lean::dec(x_27);
return x_9;
}
}
}
else
{
unsigned x_46; obj* x_47; obj* x_48; obj* x_49; 
x_46 = lean::string_iterator_curr(x_1);
x_47 = lean::box_uint32(x_46);
x_48 = lean::box_uint32(x_0);
x_49 = lean::nat_dec_eq(x_47, x_48);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_63; 
lean::dec(x_47);
lean::dec(x_49);
x_53 = l_char_quote__core(x_46);
x_54 = l_char_has__repr___closed__1;
lean::inc(x_54);
x_56 = lean::string_append(x_54, x_53);
lean::dec(x_53);
x_58 = lean::string_append(x_56, x_54);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
lean::inc(x_59);
lean::inc(x_60);
x_63 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_58, x_60, x_59, x_59, x_1);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_68; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_63, 2);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
lean::dec(x_66);
lean::dec(x_64);
lean::dec(x_68);
return x_63;
}
else
{
obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_63);
x_74 = lean::cnstr_get(x_68, 0);
lean::inc(x_74);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_76 = x_68;
}
lean::inc(x_60);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_78, 0, x_60);
lean::closure_set(x_78, 1, x_74);
if (lean::is_scalar(x_76)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_76;
}
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_64);
lean::cnstr_set(x_80, 1, x_66);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
}
else
{
obj* x_81; unsigned char x_83; 
x_81 = lean::cnstr_get(x_63, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<unsigned char>(x_63, sizeof(void*)*1);
if (x_83 == 0)
{
obj* x_85; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_63);
x_85 = lean::cnstr_get(x_81, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_81, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_81, 2);
lean::inc(x_89);
lean::inc(x_60);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_92, 0, x_60);
lean::closure_set(x_92, 1, x_89);
x_93 = lean::cnstr_get(x_81, 3);
lean::inc(x_93);
lean::dec(x_81);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_85);
lean::cnstr_set(x_96, 1, x_87);
lean::cnstr_set(x_96, 2, x_92);
lean::cnstr_set(x_96, 3, x_93);
x_97 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_83);
x_98 = x_97;
return x_98;
}
else
{
lean::dec(x_81);
return x_63;
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_49);
x_101 = lean::string_iterator_next(x_1);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_47);
lean::cnstr_set(x_103, 1, x_101);
lean::cnstr_set(x_103, 2, x_102);
return x_103;
}
}
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__5(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__7(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__9(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__9(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__11(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__13(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__13(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__15(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14(unsigned x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__15(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__17(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__16(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = lean::string_push(x_4, x_2);
x_7 = lean::string_iterator_remaining(x_1);
x_8 = l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__17(x_7, x_6, x_1);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_4217055689__parse__mangled__name__aux___main___spec__3(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_8) == 0)
{
unsigned x_16; obj* x_18; obj* x_19; 
lean::dec(x_8);
x_16 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_18 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4(x_16, x_11);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_18);
return x_19;
}
else
{
unsigned char x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_13);
lean::dec(x_11);
x_22 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_23 = x_8;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_9);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
return x_25;
}
}
else
{
obj* x_27; obj* x_29; obj* x_31; obj* x_32; unsigned x_33; obj* x_35; obj* x_36; 
lean::dec(x_8);
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_29 = x_13;
}
lean::inc(x_4);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_4);
lean::closure_set(x_31, 1, x_27);
if (lean::is_scalar(x_29)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_29;
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_35 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6(x_33, x_11);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_32, x_35);
return x_36;
}
}
else
{
obj* x_37; unsigned char x_39; 
x_37 = lean::cnstr_get(x_8, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (x_39 == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_8);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
lean::inc(x_4);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_48, 0, x_4);
lean::closure_set(x_48, 1, x_45);
x_49 = lean::cnstr_get(x_37, 3);
lean::inc(x_49);
lean::dec(x_37);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_41);
lean::cnstr_set(x_52, 1, x_43);
lean::cnstr_set(x_52, 2, x_48);
lean::cnstr_set(x_52, 3, x_49);
x_53 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_39);
x_54 = x_53;
return x_54;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_55; obj* x_57; unsigned x_60; obj* x_62; obj* x_63; 
x_55 = lean::cnstr_get(x_8, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_8, 2);
lean::inc(x_57);
lean::dec(x_8);
x_60 = lean::unbox_uint32(x_37);
lean::dec(x_37);
x_62 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8(x_60, x_55);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_62);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_64 = x_8;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_37);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_39);
x_66 = x_65;
return x_66;
}
}
}
}
else
{
unsigned x_67; unsigned char x_68; 
x_67 = lean::string_iterator_curr(x_0);
x_68 = l_char_is__digit(x_67);
if (x_68 == 0)
{
obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_79; 
x_69 = l_char_quote__core(x_67);
x_70 = l_char_has__repr___closed__1;
lean::inc(x_70);
x_72 = lean::string_append(x_70, x_69);
lean::dec(x_69);
x_74 = lean::string_append(x_72, x_70);
x_75 = lean::box(0);
x_76 = l_mjoin___rarg___closed__1;
lean::inc(x_75);
lean::inc(x_76);
x_79 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_74, x_76, x_75, x_75, x_0);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_84; 
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 2);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
if (lean::obj_tag(x_79) == 0)
{
unsigned x_87; obj* x_89; obj* x_90; 
lean::dec(x_79);
x_87 = lean::unbox_uint32(x_80);
lean::dec(x_80);
x_89 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10(x_87, x_82);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_89);
return x_90;
}
else
{
unsigned char x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_82);
lean::dec(x_84);
x_93 = lean::cnstr_get_scalar<unsigned char>(x_79, sizeof(void*)*1);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_94 = x_79;
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_80);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
return x_96;
}
}
else
{
obj* x_98; obj* x_100; obj* x_102; obj* x_103; unsigned x_104; obj* x_106; obj* x_107; 
lean::dec(x_79);
x_98 = lean::cnstr_get(x_84, 0);
lean::inc(x_98);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 x_100 = x_84;
}
lean::inc(x_76);
x_102 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_102, 0, x_76);
lean::closure_set(x_102, 1, x_98);
if (lean::is_scalar(x_100)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_100;
}
lean::cnstr_set(x_103, 0, x_102);
x_104 = lean::unbox_uint32(x_80);
lean::dec(x_80);
x_106 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12(x_104, x_82);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_106);
return x_107;
}
}
else
{
obj* x_108; unsigned char x_110; 
x_108 = lean::cnstr_get(x_79, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get_scalar<unsigned char>(x_79, sizeof(void*)*1);
if (x_110 == 0)
{
obj* x_112; obj* x_114; obj* x_116; obj* x_119; obj* x_120; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_79);
x_112 = lean::cnstr_get(x_108, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_108, 1);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_108, 2);
lean::inc(x_116);
lean::inc(x_76);
x_119 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_119, 0, x_76);
lean::closure_set(x_119, 1, x_116);
x_120 = lean::cnstr_get(x_108, 3);
lean::inc(x_120);
lean::dec(x_108);
x_123 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_123, 0, x_112);
lean::cnstr_set(x_123, 1, x_114);
lean::cnstr_set(x_123, 2, x_119);
lean::cnstr_set(x_123, 3, x_120);
x_124 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_110);
x_125 = x_124;
return x_125;
}
else
{
if (lean::obj_tag(x_79) == 0)
{
obj* x_126; obj* x_128; unsigned x_131; obj* x_133; obj* x_134; 
x_126 = lean::cnstr_get(x_79, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_79, 2);
lean::inc(x_128);
lean::dec(x_79);
x_131 = lean::unbox_uint32(x_108);
lean::dec(x_108);
x_133 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14(x_131, x_126);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_128, x_133);
return x_134;
}
else
{
obj* x_135; obj* x_136; obj* x_137; 
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_135 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_135 = x_79;
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_108);
lean::cnstr_set_scalar(x_136, sizeof(void*)*1, x_110);
x_137 = x_136;
return x_137;
}
}
}
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::inc(x_0);
x_139 = lean::string_iterator_next(x_0);
x_140 = lean::box(0);
x_141 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__16(x_0, x_139);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_140, x_141);
return x_142;
}
}
}
}
obj* l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while1___at___private_4217055689__parse__mangled__name__aux___main___spec__3(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_8 = x_1;
}
x_9 = l_string_to__nat(x_2);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_10);
x_13 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_12);
return x_13;
}
else
{
obj* x_14; unsigned char x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get_scalar<unsigned char>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_17 = x_1;
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1, x_16);
x_19 = x_18;
return x_19;
}
}
}
obj* l_lean_parser_monad__parsec_take___at___private_4217055689__parse__mangled__name__aux___main___spec__18(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_3);
x_6 = l_string_join___closed__1;
lean::inc(x_6);
x_8 = l___private_127590107__take__aux___main___rarg(x_0, x_6, x_1);
return x_8;
}
else
{
obj* x_11; obj* x_12; obj* x_15; 
lean::dec(x_3);
lean::dec(x_0);
x_11 = l_string_join___closed__1;
x_12 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_12);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_1);
lean::cnstr_set(x_15, 2, x_12);
return x_15;
}
}
}
obj* l_match__failed___at___private_4217055689__parse__mangled__name__aux___main___spec__19(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_7; unsigned char x_8; obj* x_9; obj* x_10; 
x_1 = l_match__failed___rarg___closed__1;
x_2 = l_mjoin___rarg___closed__1;
x_3 = l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_3);
x_8 = 0;
x_9 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
x_10 = x_9;
return x_10;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__6(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__8(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__10(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__12(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_4217055689__parse__mangled__name__aux___main___spec__14(x_2, x_1);
return x_3;
}
}
obj* l___private_4217055689__parse__mangled__name__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_4217055689__parse__mangled__name__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_74862231__parse__mangled__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = l_string_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_0, x_4, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::string_iterator_remaining(x_6);
x_12 = lean::box(0);
x_13 = l___private_4217055689__parse__mangled__name__aux___main(x_11, x_12, x_6);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_14);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_13);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_16);
return x_17;
}
else
{
obj* x_18; unsigned char x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_21 = x_5;
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*1, x_20);
x_23 = x_22;
return x_23;
}
}
}
obj* l_lean_name_demangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_74862231__parse__mangled__name), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_2, x_0, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; 
lean::dec(x_5);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
void initialize_init_lean_name();
void initialize_init_lean_parser_string__literal();
static bool _G_initialized = false;
void initialize_init_lean_name__mangling() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_name();
 initialize_init_lean_parser_string__literal();
 l___private_3255790009__string_mangle__aux___main___closed__1 = _init_l___private_3255790009__string_mangle__aux___main___closed__1();
 l___private_3255790009__string_mangle__aux___main___closed__2 = _init_l___private_3255790009__string_mangle__aux___main___closed__2();
 l___private_3255790009__string_mangle__aux___main___closed__3 = _init_l___private_3255790009__string_mangle__aux___main___closed__3();
 l___private_1496486805__parse__mangled__string__aux___main___closed__1 = _init_l___private_1496486805__parse__mangled__string__aux___main___closed__1();
 l___private_1496486805__parse__mangled__string__aux___main___closed__2 = _init_l___private_1496486805__parse__mangled__string__aux___main___closed__2();
 l___private_1496486805__parse__mangled__string__aux___main___closed__3 = _init_l___private_1496486805__parse__mangled__string__aux___main___closed__3();
 l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1 = _init_l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1();
 l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1 = _init_l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1();
 l_lean_string_demangle___closed__1 = _init_l_lean_string_demangle___closed__1();
 l___private_1205956357__name_mangle__aux___main___closed__1 = _init_l___private_1205956357__name_mangle__aux___main___closed__1();
 l___private_1205956357__name_mangle__aux___main___closed__2 = _init_l___private_1205956357__name_mangle__aux___main___closed__2();
 l___private_4217055689__parse__mangled__name__aux___main___closed__1 = _init_l___private_4217055689__parse__mangled__name__aux___main___closed__1();
}
