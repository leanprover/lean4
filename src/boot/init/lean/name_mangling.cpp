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
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; unsigned x_9; obj* x_10; obj* x_12; unsigned char x_14; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
x_9 = lean::string_iterator_curr(x_1);
x_14 = l_char_is__alpha(x_9);
if (x_14 == 0)
{
unsigned char x_15; 
x_15 = l_char_is__digit(x_9);
if (x_15 == 0)
{
obj* x_16; 
x_16 = lean::box(0);
x_12 = x_16;
goto lbl_13;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_3);
x_18 = lean::string_iterator_next(x_1);
x_19 = lean::string_push(x_2, x_9);
x_0 = x_6;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
else
{
if (x_14 == 0)
{
obj* x_21; 
x_21 = lean::box(0);
x_12 = x_21;
goto lbl_13;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_3);
x_23 = lean::string_iterator_next(x_1);
x_24 = lean::string_push(x_2, x_9);
x_0 = x_6;
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
lbl_11:
{
obj* x_27; obj* x_28; unsigned char x_29; 
lean::dec(x_10);
x_27 = lean::mk_nat_obj(255u);
x_28 = lean::box_uint32(x_9);
x_29 = lean::nat_dec_lt(x_28, x_27);
lean::dec(x_27);
if (x_29 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; unsigned x_36; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; unsigned x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; unsigned x_54; obj* x_56; obj* x_57; obj* x_60; unsigned x_61; obj* x_63; obj* x_64; 
x_31 = l___private_3255790009__string_mangle__aux___main___closed__1;
x_32 = lean::string_append(x_2, x_31);
x_33 = lean::mk_nat_obj(4096u);
x_34 = lean::nat_div(x_28, x_33);
x_35 = l_nat_digit__char(x_34);
x_36 = lean::unbox_uint32(x_35);
lean::dec(x_35);
x_38 = lean::string_push(x_32, x_36);
x_39 = lean::nat_mod(x_28, x_33);
lean::dec(x_33);
lean::dec(x_28);
x_42 = lean::mk_nat_obj(256u);
x_43 = lean::nat_div(x_39, x_42);
x_44 = l_nat_digit__char(x_43);
x_45 = lean::unbox_uint32(x_44);
lean::dec(x_44);
x_47 = lean::string_push(x_38, x_45);
x_48 = lean::nat_mod(x_39, x_42);
lean::dec(x_42);
lean::dec(x_39);
x_51 = lean::mk_nat_obj(16u);
x_52 = lean::nat_div(x_48, x_51);
x_53 = l_nat_digit__char(x_52);
x_54 = lean::unbox_uint32(x_53);
lean::dec(x_53);
x_56 = lean::string_push(x_47, x_54);
x_57 = lean::nat_mod(x_48, x_51);
lean::dec(x_51);
lean::dec(x_48);
x_60 = l_nat_digit__char(x_57);
x_61 = lean::unbox_uint32(x_60);
lean::dec(x_60);
x_63 = lean::string_push(x_56, x_61);
x_64 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_64;
x_2 = x_63;
goto _start;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; unsigned x_71; obj* x_73; obj* x_74; obj* x_77; unsigned x_78; obj* x_80; obj* x_81; 
x_66 = l___private_3255790009__string_mangle__aux___main___closed__2;
x_67 = lean::string_append(x_2, x_66);
x_68 = lean::mk_nat_obj(16u);
x_69 = lean::nat_div(x_28, x_68);
x_70 = l_nat_digit__char(x_69);
x_71 = lean::unbox_uint32(x_70);
lean::dec(x_70);
x_73 = lean::string_push(x_67, x_71);
x_74 = lean::nat_mod(x_28, x_68);
lean::dec(x_68);
lean::dec(x_28);
x_77 = l_nat_digit__char(x_74);
x_78 = lean::unbox_uint32(x_77);
lean::dec(x_77);
x_80 = lean::string_push(x_73, x_78);
x_81 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_81;
x_2 = x_80;
goto _start;
}
}
lbl_13:
{
obj* x_84; obj* x_85; unsigned char x_86; unsigned x_88; 
lean::dec(x_12);
x_84 = lean::mk_nat_obj(95u);
x_85 = lean::mk_nat_obj(55296u);
x_86 = lean::nat_dec_lt(x_84, x_85);
lean::dec(x_85);
if (x_86 == 0)
{
obj* x_90; unsigned char x_91; 
x_90 = lean::mk_nat_obj(57343u);
x_91 = lean::nat_dec_lt(x_90, x_84);
lean::dec(x_90);
if (x_91 == 0)
{
unsigned x_94; 
lean::dec(x_84);
x_94 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_88 = x_94;
goto lbl_89;
}
else
{
obj* x_96; unsigned char x_97; 
x_96 = lean::mk_nat_obj(1114112u);
x_97 = lean::nat_dec_lt(x_84, x_96);
lean::dec(x_96);
if (x_97 == 0)
{
unsigned x_100; 
lean::dec(x_84);
x_100 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_88 = x_100;
goto lbl_89;
}
else
{
unsigned x_103; 
lean::dec(x_3);
x_103 = lean::unbox_uint32(x_84);
lean::dec(x_84);
x_88 = x_103;
goto lbl_89;
}
}
}
else
{
unsigned x_106; 
lean::dec(x_3);
x_106 = lean::unbox_uint32(x_84);
lean::dec(x_84);
x_88 = x_106;
goto lbl_89;
}
lbl_89:
{
obj* x_108; obj* x_109; unsigned char x_110; 
x_108 = lean::box_uint32(x_9);
x_109 = lean::box_uint32(x_88);
x_110 = lean::nat_dec_eq(x_108, x_109);
lean::dec(x_109);
lean::dec(x_108);
if (x_110 == 0)
{
obj* x_113; 
x_113 = lean::box(0);
x_10 = x_113;
goto lbl_11;
}
else
{
obj* x_114; obj* x_115; obj* x_116; 
x_114 = lean::string_iterator_next(x_1);
x_115 = l___private_3255790009__string_mangle__aux___main___closed__3;
x_116 = lean::string_append(x_2, x_115);
x_0 = x_6;
x_1 = x_114;
x_2 = x_116;
goto _start;
}
}
}
}
else
{
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
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_12; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
lean::inc(x_2);
x_12 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 2);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_17 = x_12;
}
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_18);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_9 = x_22;
goto lbl_10;
}
else
{
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_26 = x_12;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
x_9 = x_28;
goto lbl_10;
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_33; unsigned char x_35; obj* x_36; obj* x_37; unsigned char x_38; 
x_33 = lean::cnstr_get(x_9, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
if (x_35 == 0)
{
obj* x_42; 
lean::dec(x_9);
lean::inc(x_2);
x_42 = l_lean_parser_monad__parsec_alpha___at___private_1496486805__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; unsigned x_50; obj* x_53; obj* x_55; obj* x_56; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 2);
lean::inc(x_47);
lean::dec(x_42);
x_50 = lean::unbox_uint32(x_43);
lean::dec(x_43);
lean::inc(x_1);
x_53 = lean::string_push(x_1, x_50);
lean::inc(x_6);
x_55 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_53, x_45);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_61; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_61 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_56);
return x_61;
}
else
{
obj* x_62; unsigned char x_64; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<unsigned char>(x_56, sizeof(void*)*1);
x_36 = x_56;
x_37 = x_62;
x_38 = x_64;
goto lbl_39;
}
}
else
{
obj* x_65; unsigned char x_67; obj* x_68; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_42, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<unsigned char>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_68 = x_42;
}
lean::inc(x_65);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_65);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_67);
x_71 = x_70;
x_36 = x_71;
x_37 = x_65;
x_38 = x_67;
goto lbl_39;
}
}
else
{
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_33);
return x_9;
}
lbl_39:
{
obj* x_77; obj* x_78; unsigned char x_79; 
if (x_38 == 0)
{
obj* x_83; 
lean::dec(x_36);
lean::inc(x_2);
x_83 = l_lean_parser_monad__parsec_digit___at___private_1496486805__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_88; unsigned x_91; obj* x_94; obj* x_96; obj* x_97; 
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 2);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::unbox_uint32(x_84);
lean::dec(x_84);
lean::inc(x_1);
x_94 = lean::string_push(x_1, x_91);
lean::inc(x_6);
x_96 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_94, x_86);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_102; obj* x_103; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_102 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_97);
x_103 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_102);
return x_103;
}
else
{
obj* x_104; unsigned char x_106; 
x_104 = lean::cnstr_get(x_97, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<unsigned char>(x_97, sizeof(void*)*1);
x_77 = x_97;
x_78 = x_104;
x_79 = x_106;
goto lbl_80;
}
}
else
{
obj* x_107; unsigned char x_109; obj* x_110; obj* x_112; obj* x_113; 
x_107 = lean::cnstr_get(x_83, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<unsigned char>(x_83, sizeof(void*)*1);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_110 = x_83;
}
lean::inc(x_107);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_109);
x_113 = x_112;
x_77 = x_113;
x_78 = x_107;
x_79 = x_109;
goto lbl_80;
}
}
else
{
obj* x_119; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_37);
x_119 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_36);
return x_119;
}
lbl_80:
{
obj* x_120; obj* x_121; unsigned char x_122; 
if (x_79 == 0)
{
obj* x_125; obj* x_126; obj* x_130; 
lean::dec(x_77);
x_125 = l___private_3255790009__string_mangle__aux___main___closed__3;
x_126 = l___private_1496486805__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
lean::inc(x_126);
lean::inc(x_125);
x_130 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_125, x_126, x_2);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; obj* x_133; obj* x_136; obj* x_137; unsigned char x_138; 
x_131 = lean::cnstr_get(x_130, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_130, 2);
lean::inc(x_133);
lean::dec(x_130);
x_136 = lean::mk_nat_obj(95u);
x_137 = lean::mk_nat_obj(55296u);
x_138 = lean::nat_dec_lt(x_136, x_137);
lean::dec(x_137);
if (x_138 == 0)
{
obj* x_140; unsigned char x_141; 
x_140 = lean::mk_nat_obj(57343u);
x_141 = lean::nat_dec_lt(x_140, x_136);
lean::dec(x_140);
if (x_141 == 0)
{
unsigned x_144; obj* x_146; obj* x_148; obj* x_149; 
lean::dec(x_136);
x_144 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_146 = lean::string_push(x_1, x_144);
lean::inc(x_6);
x_148 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_146, x_131);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_148);
if (lean::obj_tag(x_149) == 0)
{
obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_154 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_149);
x_155 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_154);
x_156 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_155);
return x_156;
}
else
{
obj* x_157; unsigned char x_159; 
x_157 = lean::cnstr_get(x_149, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get_scalar<unsigned char>(x_149, sizeof(void*)*1);
x_120 = x_149;
x_121 = x_157;
x_122 = x_159;
goto lbl_123;
}
}
else
{
obj* x_160; unsigned char x_161; 
x_160 = lean::mk_nat_obj(1114112u);
x_161 = lean::nat_dec_lt(x_136, x_160);
lean::dec(x_160);
if (x_161 == 0)
{
unsigned x_164; obj* x_166; obj* x_168; obj* x_169; 
lean::dec(x_136);
x_164 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_166 = lean::string_push(x_1, x_164);
lean::inc(x_6);
x_168 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_166, x_131);
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_168);
if (lean::obj_tag(x_169) == 0)
{
obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_174 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_169);
x_175 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_174);
x_176 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_175);
return x_176;
}
else
{
obj* x_177; unsigned char x_179; 
x_177 = lean::cnstr_get(x_169, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get_scalar<unsigned char>(x_169, sizeof(void*)*1);
x_120 = x_169;
x_121 = x_177;
x_122 = x_179;
goto lbl_123;
}
}
else
{
unsigned x_180; obj* x_183; obj* x_185; obj* x_186; 
x_180 = lean::unbox_uint32(x_136);
lean::dec(x_136);
lean::inc(x_1);
x_183 = lean::string_push(x_1, x_180);
lean::inc(x_6);
x_185 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_183, x_131);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_185);
if (lean::obj_tag(x_186) == 0)
{
obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_191 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_186);
x_192 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_191);
x_193 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_192);
return x_193;
}
else
{
obj* x_194; unsigned char x_196; 
x_194 = lean::cnstr_get(x_186, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get_scalar<unsigned char>(x_186, sizeof(void*)*1);
x_120 = x_186;
x_121 = x_194;
x_122 = x_196;
goto lbl_123;
}
}
}
}
else
{
unsigned x_197; obj* x_200; obj* x_202; obj* x_203; 
x_197 = lean::unbox_uint32(x_136);
lean::dec(x_136);
lean::inc(x_1);
x_200 = lean::string_push(x_1, x_197);
lean::inc(x_6);
x_202 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_200, x_131);
x_203 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_202);
if (lean::obj_tag(x_203) == 0)
{
obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_203);
x_209 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_208);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_209);
return x_210;
}
else
{
obj* x_211; unsigned char x_213; 
x_211 = lean::cnstr_get(x_203, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get_scalar<unsigned char>(x_203, sizeof(void*)*1);
x_120 = x_203;
x_121 = x_211;
x_122 = x_213;
goto lbl_123;
}
}
}
else
{
obj* x_214; unsigned char x_216; obj* x_217; obj* x_219; obj* x_220; 
x_214 = lean::cnstr_get(x_130, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get_scalar<unsigned char>(x_130, sizeof(void*)*1);
if (lean::is_shared(x_130)) {
 lean::dec(x_130);
 x_217 = lean::box(0);
} else {
 lean::cnstr_release(x_130, 0);
 x_217 = x_130;
}
lean::inc(x_214);
if (lean::is_scalar(x_217)) {
 x_219 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_219 = x_217;
}
lean::cnstr_set(x_219, 0, x_214);
lean::cnstr_set_scalar(x_219, sizeof(void*)*1, x_216);
x_220 = x_219;
x_120 = x_220;
x_121 = x_214;
x_122 = x_216;
goto lbl_123;
}
}
else
{
obj* x_226; obj* x_227; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_78);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_77);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_226);
return x_227;
}
lbl_123:
{
obj* x_228; obj* x_229; unsigned char x_230; 
if (x_122 == 0)
{
obj* x_233; obj* x_234; obj* x_238; 
lean::dec(x_120);
x_233 = l___private_3255790009__string_mangle__aux___main___closed__2;
x_234 = l___private_1496486805__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_234);
lean::inc(x_233);
x_238 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_233, x_234, x_2);
if (lean::obj_tag(x_238) == 0)
{
obj* x_239; obj* x_241; obj* x_244; 
x_239 = lean::cnstr_get(x_238, 1);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_238, 2);
lean::inc(x_241);
lean::dec(x_238);
x_244 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_239);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_249; obj* x_252; 
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_244, 2);
lean::inc(x_249);
lean::dec(x_244);
x_252 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_247);
if (lean::obj_tag(x_252) == 0)
{
obj* x_253; obj* x_255; obj* x_257; obj* x_260; obj* x_261; obj* x_264; obj* x_267; unsigned char x_268; 
x_253 = lean::cnstr_get(x_252, 0);
lean::inc(x_253);
x_255 = lean::cnstr_get(x_252, 1);
lean::inc(x_255);
x_257 = lean::cnstr_get(x_252, 2);
lean::inc(x_257);
lean::dec(x_252);
x_260 = lean::mk_nat_obj(16u);
x_261 = lean::nat_mul(x_245, x_260);
lean::dec(x_260);
lean::dec(x_245);
x_264 = lean::nat_add(x_261, x_253);
lean::dec(x_253);
lean::dec(x_261);
x_267 = lean::mk_nat_obj(55296u);
x_268 = lean::nat_dec_lt(x_264, x_267);
lean::dec(x_267);
if (x_268 == 0)
{
obj* x_270; unsigned char x_271; 
x_270 = lean::mk_nat_obj(57343u);
x_271 = lean::nat_dec_lt(x_270, x_264);
lean::dec(x_270);
if (x_271 == 0)
{
unsigned x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
lean::dec(x_264);
x_274 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_276 = lean::string_push(x_1, x_274);
lean::inc(x_6);
x_278 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_276, x_255);
x_279 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_278);
x_280 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_279);
x_281 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_280);
if (lean::obj_tag(x_281) == 0)
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_281);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_286);
x_288 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_287);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_288);
return x_289;
}
else
{
obj* x_290; unsigned char x_292; 
x_290 = lean::cnstr_get(x_281, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get_scalar<unsigned char>(x_281, sizeof(void*)*1);
x_228 = x_281;
x_229 = x_290;
x_230 = x_292;
goto lbl_231;
}
}
else
{
obj* x_293; unsigned char x_294; 
x_293 = lean::mk_nat_obj(1114112u);
x_294 = lean::nat_dec_lt(x_264, x_293);
lean::dec(x_293);
if (x_294 == 0)
{
unsigned x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
lean::dec(x_264);
x_297 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_299 = lean::string_push(x_1, x_297);
lean::inc(x_6);
x_301 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_299, x_255);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_301);
x_303 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_302);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_303);
if (lean::obj_tag(x_304) == 0)
{
obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_309 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_304);
x_310 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_309);
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_310);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_311);
return x_312;
}
else
{
obj* x_313; unsigned char x_315; 
x_313 = lean::cnstr_get(x_304, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get_scalar<unsigned char>(x_304, sizeof(void*)*1);
x_228 = x_304;
x_229 = x_313;
x_230 = x_315;
goto lbl_231;
}
}
else
{
unsigned x_316; obj* x_319; obj* x_321; obj* x_322; obj* x_323; obj* x_324; 
x_316 = lean::unbox_uint32(x_264);
lean::dec(x_264);
lean::inc(x_1);
x_319 = lean::string_push(x_1, x_316);
lean::inc(x_6);
x_321 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_319, x_255);
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_321);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_322);
x_324 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_323);
if (lean::obj_tag(x_324) == 0)
{
obj* x_329; obj* x_330; obj* x_331; obj* x_332; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_324);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_329);
x_331 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_330);
x_332 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_331);
return x_332;
}
else
{
obj* x_333; unsigned char x_335; 
x_333 = lean::cnstr_get(x_324, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get_scalar<unsigned char>(x_324, sizeof(void*)*1);
x_228 = x_324;
x_229 = x_333;
x_230 = x_335;
goto lbl_231;
}
}
}
}
else
{
unsigned x_336; obj* x_339; obj* x_341; obj* x_342; obj* x_343; obj* x_344; 
x_336 = lean::unbox_uint32(x_264);
lean::dec(x_264);
lean::inc(x_1);
x_339 = lean::string_push(x_1, x_336);
lean::inc(x_6);
x_341 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_339, x_255);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_342);
x_344 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_343);
if (lean::obj_tag(x_344) == 0)
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_344);
x_350 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_349);
x_351 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_350);
x_352 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_351);
return x_352;
}
else
{
obj* x_353; unsigned char x_355; 
x_353 = lean::cnstr_get(x_344, 0);
lean::inc(x_353);
x_355 = lean::cnstr_get_scalar<unsigned char>(x_344, sizeof(void*)*1);
x_228 = x_344;
x_229 = x_353;
x_230 = x_355;
goto lbl_231;
}
}
}
else
{
obj* x_357; unsigned char x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
lean::dec(x_245);
x_357 = lean::cnstr_get(x_252, 0);
lean::inc(x_357);
x_359 = lean::cnstr_get_scalar<unsigned char>(x_252, sizeof(void*)*1);
if (lean::is_shared(x_252)) {
 lean::dec(x_252);
 x_360 = lean::box(0);
} else {
 lean::cnstr_release(x_252, 0);
 x_360 = x_252;
}
if (lean::is_scalar(x_360)) {
 x_361 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_361 = x_360;
}
lean::cnstr_set(x_361, 0, x_357);
lean::cnstr_set_scalar(x_361, sizeof(void*)*1, x_359);
x_362 = x_361;
x_363 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_362);
x_364 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_363);
if (lean::obj_tag(x_364) == 0)
{
obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_369 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_364);
x_370 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_369);
x_371 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_370);
x_372 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_371);
return x_372;
}
else
{
obj* x_373; unsigned char x_375; 
x_373 = lean::cnstr_get(x_364, 0);
lean::inc(x_373);
x_375 = lean::cnstr_get_scalar<unsigned char>(x_364, sizeof(void*)*1);
x_228 = x_364;
x_229 = x_373;
x_230 = x_375;
goto lbl_231;
}
}
}
else
{
obj* x_376; unsigned char x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; 
x_376 = lean::cnstr_get(x_244, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get_scalar<unsigned char>(x_244, sizeof(void*)*1);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_379 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_379 = x_244;
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_376);
lean::cnstr_set_scalar(x_380, sizeof(void*)*1, x_378);
x_381 = x_380;
x_382 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_381);
if (lean::obj_tag(x_382) == 0)
{
obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_382);
x_388 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_387);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_388);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_389);
return x_390;
}
else
{
obj* x_391; unsigned char x_393; 
x_391 = lean::cnstr_get(x_382, 0);
lean::inc(x_391);
x_393 = lean::cnstr_get_scalar<unsigned char>(x_382, sizeof(void*)*1);
x_228 = x_382;
x_229 = x_391;
x_230 = x_393;
goto lbl_231;
}
}
}
else
{
obj* x_394; unsigned char x_396; obj* x_397; obj* x_399; obj* x_400; 
x_394 = lean::cnstr_get(x_238, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get_scalar<unsigned char>(x_238, sizeof(void*)*1);
if (lean::is_shared(x_238)) {
 lean::dec(x_238);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_238, 0);
 x_397 = x_238;
}
lean::inc(x_394);
if (lean::is_scalar(x_397)) {
 x_399 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_399 = x_397;
}
lean::cnstr_set(x_399, 0, x_394);
lean::cnstr_set_scalar(x_399, sizeof(void*)*1, x_396);
x_400 = x_399;
x_228 = x_400;
x_229 = x_394;
x_230 = x_396;
goto lbl_231;
}
}
else
{
obj* x_406; obj* x_407; obj* x_408; 
lean::dec(x_121);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_406 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_120);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_407);
return x_408;
}
lbl_231:
{
if (x_230 == 0)
{
obj* x_410; obj* x_411; obj* x_414; 
lean::dec(x_228);
x_410 = l___private_3255790009__string_mangle__aux___main___closed__1;
x_411 = l___private_1496486805__parse__mangled__string__aux___main___closed__1;
lean::inc(x_411);
lean::inc(x_410);
x_414 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_410, x_411, x_2);
if (lean::obj_tag(x_414) == 0)
{
obj* x_415; obj* x_417; obj* x_420; 
x_415 = lean::cnstr_get(x_414, 1);
lean::inc(x_415);
x_417 = lean::cnstr_get(x_414, 2);
lean::inc(x_417);
lean::dec(x_414);
x_420 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_415);
if (lean::obj_tag(x_420) == 0)
{
obj* x_421; obj* x_423; obj* x_425; obj* x_428; 
x_421 = lean::cnstr_get(x_420, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_420, 1);
lean::inc(x_423);
x_425 = lean::cnstr_get(x_420, 2);
lean::inc(x_425);
lean::dec(x_420);
x_428 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_423);
if (lean::obj_tag(x_428) == 0)
{
obj* x_429; obj* x_431; obj* x_433; obj* x_436; 
x_429 = lean::cnstr_get(x_428, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_428, 1);
lean::inc(x_431);
x_433 = lean::cnstr_get(x_428, 2);
lean::inc(x_433);
lean::dec(x_428);
x_436 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_431);
if (lean::obj_tag(x_436) == 0)
{
obj* x_437; obj* x_439; obj* x_441; obj* x_444; 
x_437 = lean::cnstr_get(x_436, 0);
lean::inc(x_437);
x_439 = lean::cnstr_get(x_436, 1);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_436, 2);
lean::inc(x_441);
lean::dec(x_436);
x_444 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2(x_439);
if (lean::obj_tag(x_444) == 0)
{
obj* x_445; obj* x_447; obj* x_449; obj* x_452; obj* x_453; obj* x_456; obj* x_457; obj* x_460; obj* x_463; obj* x_464; obj* x_467; obj* x_470; obj* x_473; unsigned char x_474; 
x_445 = lean::cnstr_get(x_444, 0);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_444, 1);
lean::inc(x_447);
x_449 = lean::cnstr_get(x_444, 2);
lean::inc(x_449);
lean::dec(x_444);
x_452 = lean::mk_nat_obj(4096u);
x_453 = lean::nat_mul(x_421, x_452);
lean::dec(x_452);
lean::dec(x_421);
x_456 = lean::mk_nat_obj(256u);
x_457 = lean::nat_mul(x_429, x_456);
lean::dec(x_456);
lean::dec(x_429);
x_460 = lean::nat_add(x_453, x_457);
lean::dec(x_457);
lean::dec(x_453);
x_463 = lean::mk_nat_obj(16u);
x_464 = lean::nat_mul(x_437, x_463);
lean::dec(x_463);
lean::dec(x_437);
x_467 = lean::nat_add(x_460, x_464);
lean::dec(x_464);
lean::dec(x_460);
x_470 = lean::nat_add(x_467, x_445);
lean::dec(x_445);
lean::dec(x_467);
x_473 = lean::mk_nat_obj(55296u);
x_474 = lean::nat_dec_lt(x_470, x_473);
lean::dec(x_473);
if (x_474 == 0)
{
obj* x_476; unsigned char x_477; 
x_476 = lean::mk_nat_obj(57343u);
x_477 = lean::nat_dec_lt(x_476, x_470);
lean::dec(x_476);
if (x_477 == 0)
{
unsigned x_480; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; 
lean::dec(x_470);
x_480 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_482 = lean::string_push(x_1, x_480);
x_483 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_482, x_447);
x_484 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_449, x_483);
x_485 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_484);
x_486 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_485);
x_487 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_486);
x_488 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_487);
x_489 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_488);
x_490 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_489);
x_491 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_490);
x_492 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_491);
x_493 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_492);
return x_493;
}
else
{
obj* x_494; unsigned char x_495; 
x_494 = lean::mk_nat_obj(1114112u);
x_495 = lean::nat_dec_lt(x_470, x_494);
lean::dec(x_494);
if (x_495 == 0)
{
unsigned x_498; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; 
lean::dec(x_470);
x_498 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_500 = lean::string_push(x_1, x_498);
x_501 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_500, x_447);
x_502 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_449, x_501);
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_502);
x_504 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_503);
x_505 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_504);
x_506 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_505);
x_507 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_506);
x_508 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_507);
x_509 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_508);
x_510 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_509);
x_511 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_510);
return x_511;
}
else
{
unsigned x_513; obj* x_515; obj* x_516; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; 
lean::dec(x_3);
x_513 = lean::unbox_uint32(x_470);
lean::dec(x_470);
x_515 = lean::string_push(x_1, x_513);
x_516 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_515, x_447);
x_517 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_449, x_516);
x_518 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_517);
x_519 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_518);
x_520 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_519);
x_521 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_520);
x_522 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_521);
x_523 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_522);
x_524 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_523);
x_525 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_524);
x_526 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_525);
return x_526;
}
}
}
else
{
unsigned x_528; obj* x_530; obj* x_531; obj* x_532; obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; 
lean::dec(x_3);
x_528 = lean::unbox_uint32(x_470);
lean::dec(x_470);
x_530 = lean::string_push(x_1, x_528);
x_531 = l___private_1496486805__parse__mangled__string__aux___main(x_6, x_530, x_447);
x_532 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_449, x_531);
x_533 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_532);
x_534 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_533);
x_535 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_534);
x_536 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_535);
x_537 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_536);
x_538 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_537);
x_539 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_538);
x_540 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_539);
x_541 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_540);
return x_541;
}
}
else
{
obj* x_548; unsigned char x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_561; obj* x_562; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_429);
lean::dec(x_421);
lean::dec(x_437);
x_548 = lean::cnstr_get(x_444, 0);
lean::inc(x_548);
x_550 = lean::cnstr_get_scalar<unsigned char>(x_444, sizeof(void*)*1);
if (lean::is_shared(x_444)) {
 lean::dec(x_444);
 x_551 = lean::box(0);
} else {
 lean::cnstr_release(x_444, 0);
 x_551 = x_444;
}
if (lean::is_scalar(x_551)) {
 x_552 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_552 = x_551;
}
lean::cnstr_set(x_552, 0, x_548);
lean::cnstr_set_scalar(x_552, sizeof(void*)*1, x_550);
x_553 = x_552;
x_554 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_553);
x_555 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_554);
x_556 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_555);
x_557 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_556);
x_558 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_557);
x_559 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_558);
x_560 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_559);
x_561 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_560);
x_562 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_561);
return x_562;
}
}
else
{
obj* x_568; unsigned char x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_429);
lean::dec(x_421);
x_568 = lean::cnstr_get(x_436, 0);
lean::inc(x_568);
x_570 = lean::cnstr_get_scalar<unsigned char>(x_436, sizeof(void*)*1);
if (lean::is_shared(x_436)) {
 lean::dec(x_436);
 x_571 = lean::box(0);
} else {
 lean::cnstr_release(x_436, 0);
 x_571 = x_436;
}
if (lean::is_scalar(x_571)) {
 x_572 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_572 = x_571;
}
lean::cnstr_set(x_572, 0, x_568);
lean::cnstr_set_scalar(x_572, sizeof(void*)*1, x_570);
x_573 = x_572;
x_574 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_433, x_573);
x_575 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_574);
x_576 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_575);
x_577 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_576);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_577);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_578);
x_580 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_579);
x_581 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_580);
return x_581;
}
}
else
{
obj* x_586; unsigned char x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_421);
x_586 = lean::cnstr_get(x_428, 0);
lean::inc(x_586);
x_588 = lean::cnstr_get_scalar<unsigned char>(x_428, sizeof(void*)*1);
if (lean::is_shared(x_428)) {
 lean::dec(x_428);
 x_589 = lean::box(0);
} else {
 lean::cnstr_release(x_428, 0);
 x_589 = x_428;
}
if (lean::is_scalar(x_589)) {
 x_590 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_590 = x_589;
}
lean::cnstr_set(x_590, 0, x_586);
lean::cnstr_set_scalar(x_590, sizeof(void*)*1, x_588);
x_591 = x_590;
x_592 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_591);
x_593 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_592);
x_594 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_593);
x_595 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_594);
x_596 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_595);
x_597 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_596);
x_598 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_597);
return x_598;
}
}
else
{
obj* x_602; unsigned char x_604; obj* x_605; obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_602 = lean::cnstr_get(x_420, 0);
lean::inc(x_602);
x_604 = lean::cnstr_get_scalar<unsigned char>(x_420, sizeof(void*)*1);
if (lean::is_shared(x_420)) {
 lean::dec(x_420);
 x_605 = lean::box(0);
} else {
 lean::cnstr_release(x_420, 0);
 x_605 = x_420;
}
if (lean::is_scalar(x_605)) {
 x_606 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_606 = x_605;
}
lean::cnstr_set(x_606, 0, x_602);
lean::cnstr_set_scalar(x_606, sizeof(void*)*1, x_604);
x_607 = x_606;
x_608 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_607);
x_609 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_608);
x_610 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_609);
x_611 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_610);
x_612 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_611);
x_613 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_612);
return x_613;
}
}
else
{
obj* x_617; unsigned char x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; obj* x_627; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_617 = lean::cnstr_get(x_414, 0);
lean::inc(x_617);
x_619 = lean::cnstr_get_scalar<unsigned char>(x_414, sizeof(void*)*1);
if (lean::is_shared(x_414)) {
 lean::dec(x_414);
 x_620 = lean::box(0);
} else {
 lean::cnstr_release(x_414, 0);
 x_620 = x_414;
}
if (lean::is_scalar(x_620)) {
 x_621 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_621 = x_620;
}
lean::cnstr_set(x_621, 0, x_617);
lean::cnstr_set_scalar(x_621, sizeof(void*)*1, x_619);
x_622 = x_621;
x_623 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_622);
x_624 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_623);
x_625 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_624);
x_626 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_625);
x_627 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_626);
return x_627;
}
}
else
{
obj* x_633; obj* x_634; obj* x_635; obj* x_636; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_229);
x_633 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_228);
x_634 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_633);
x_635 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_634);
x_636 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_635);
return x_636;
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
obj* x_639; obj* x_641; 
lean::dec(x_3);
lean::dec(x_0);
x_639 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_639);
x_641 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_641, 0, x_1);
lean::cnstr_set(x_641, 1, x_2);
lean::cnstr_set(x_641, 2, x_639);
return x_641;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; unsigned char x_16; 
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
if (x_16 == 0)
{
obj* x_18; unsigned char x_19; 
x_18 = lean::mk_nat_obj(57343u);
x_19 = lean::nat_dec_lt(x_18, x_14);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_14);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::nat_sub(x_7, x_22);
lean::dec(x_22);
lean::dec(x_7);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_26);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_0);
x_31 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_31);
x_33 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_29, x_31);
return x_33;
}
else
{
obj* x_34; unsigned char x_36; 
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_29, sizeof(void*)*1);
x_1 = x_29;
x_2 = x_34;
x_3 = x_36;
goto lbl_4;
}
}
else
{
obj* x_37; unsigned char x_38; 
x_37 = lean::mk_nat_obj(1114112u);
x_38 = lean::nat_dec_lt(x_14, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_42; obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_14);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::nat_sub(x_7, x_41);
lean::dec(x_41);
lean::dec(x_7);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_45);
if (lean::is_scalar(x_13)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_13;
}
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_9);
lean::cnstr_set(x_47, 2, x_45);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; obj* x_52; 
lean::dec(x_0);
x_50 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_50);
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_48, x_50);
return x_52;
}
else
{
obj* x_53; unsigned char x_55; 
x_53 = lean::cnstr_get(x_48, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
x_1 = x_48;
x_2 = x_53;
x_3 = x_55;
goto lbl_4;
}
}
else
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; 
x_56 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
if (lean::is_scalar(x_13)) {
 x_61 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_61 = x_13;
}
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_9);
lean::cnstr_set(x_61, 2, x_59);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_0);
x_64 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_64);
x_66 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_62, x_64);
return x_66;
}
else
{
obj* x_67; unsigned char x_69; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get_scalar<unsigned char>(x_62, sizeof(void*)*1);
x_1 = x_62;
x_2 = x_67;
x_3 = x_69;
goto lbl_4;
}
}
}
}
else
{
obj* x_70; obj* x_73; obj* x_75; obj* x_76; 
x_70 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
if (lean::is_scalar(x_13)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_13;
}
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set(x_75, 1, x_9);
lean::cnstr_set(x_75, 2, x_73);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_78; obj* x_80; 
lean::dec(x_0);
x_78 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_76, x_78);
return x_80;
}
else
{
obj* x_81; unsigned char x_83; 
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<unsigned char>(x_76, sizeof(void*)*1);
x_1 = x_76;
x_2 = x_81;
x_3 = x_83;
goto lbl_4;
}
}
}
else
{
obj* x_84; unsigned char x_86; obj* x_87; obj* x_89; obj* x_90; 
x_84 = lean::cnstr_get(x_6, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_87 = x_6;
}
lean::inc(x_84);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_84);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_86);
x_90 = x_89;
x_1 = x_90;
x_2 = x_84;
x_3 = x_86;
goto lbl_4;
}
lbl_4:
{
obj* x_91; obj* x_92; unsigned char x_93; 
if (x_3 == 0)
{
obj* x_96; unsigned char x_98; 
lean::dec(x_1);
x_98 = lean::string_iterator_has_next(x_0);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_106; 
x_99 = lean::box(0);
x_100 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_101 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_99);
lean::inc(x_101);
lean::inc(x_100);
x_106 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_100, x_101, x_99, x_99, x_0);
x_96 = x_106;
goto lbl_97;
}
else
{
unsigned x_107; obj* x_108; obj* x_110; obj* x_112; obj* x_113; unsigned char x_114; unsigned char x_115; 
x_107 = lean::string_iterator_curr(x_0);
x_112 = lean::mk_nat_obj(97u);
x_113 = lean::mk_nat_obj(55296u);
x_114 = lean::nat_dec_lt(x_112, x_113);
if (x_114 == 0)
{
obj* x_117; unsigned char x_118; 
x_117 = lean::mk_nat_obj(57343u);
x_118 = lean::nat_dec_lt(x_117, x_112);
lean::dec(x_117);
if (x_118 == 0)
{
obj* x_121; obj* x_122; unsigned char x_123; 
lean::dec(x_112);
x_121 = lean::mk_nat_obj(0u);
x_122 = lean::box_uint32(x_107);
x_123 = lean::nat_dec_le(x_121, x_122);
lean::dec(x_122);
lean::dec(x_121);
if (x_123 == 0)
{
obj* x_127; 
lean::dec(x_113);
x_127 = lean::box(0);
x_108 = x_127;
goto lbl_109;
}
else
{
unsigned char x_128; 
x_128 = 1;
x_115 = x_128;
goto lbl_116;
}
}
else
{
obj* x_129; unsigned char x_130; 
x_129 = lean::mk_nat_obj(1114112u);
x_130 = lean::nat_dec_lt(x_112, x_129);
lean::dec(x_129);
if (x_130 == 0)
{
obj* x_133; obj* x_134; unsigned char x_135; 
lean::dec(x_112);
x_133 = lean::mk_nat_obj(0u);
x_134 = lean::box_uint32(x_107);
x_135 = lean::nat_dec_le(x_133, x_134);
lean::dec(x_134);
lean::dec(x_133);
if (x_135 == 0)
{
obj* x_139; 
lean::dec(x_113);
x_139 = lean::box(0);
x_108 = x_139;
goto lbl_109;
}
else
{
unsigned char x_140; 
x_140 = 1;
x_115 = x_140;
goto lbl_116;
}
}
else
{
obj* x_141; unsigned char x_142; 
x_141 = lean::box_uint32(x_107);
x_142 = lean::nat_dec_le(x_112, x_141);
lean::dec(x_141);
lean::dec(x_112);
if (x_142 == 0)
{
obj* x_146; 
lean::dec(x_113);
x_146 = lean::box(0);
x_108 = x_146;
goto lbl_109;
}
else
{
unsigned char x_147; 
x_147 = 1;
x_115 = x_147;
goto lbl_116;
}
}
}
}
else
{
obj* x_148; unsigned char x_149; 
x_148 = lean::box_uint32(x_107);
x_149 = lean::nat_dec_le(x_112, x_148);
lean::dec(x_148);
lean::dec(x_112);
if (x_149 == 0)
{
obj* x_153; 
lean::dec(x_113);
x_153 = lean::box(0);
x_108 = x_153;
goto lbl_109;
}
else
{
unsigned char x_154; 
x_154 = 1;
x_115 = x_154;
goto lbl_116;
}
}
lbl_109:
{
obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_167; 
lean::dec(x_108);
x_156 = l_char_quote__core(x_107);
x_157 = l_char_has__repr___closed__1;
lean::inc(x_157);
x_159 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_161 = lean::string_append(x_159, x_157);
x_162 = lean::box(0);
x_163 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_162);
lean::inc(x_163);
x_167 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_161, x_163, x_162, x_162, x_0);
x_96 = x_167;
goto lbl_97;
}
lbl_111:
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_110);
lean::inc(x_0);
x_170 = lean::string_iterator_next(x_0);
x_171 = lean::box(0);
x_172 = lean::box_uint32(x_107);
x_173 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_170);
lean::cnstr_set(x_173, 2, x_171);
x_96 = x_173;
goto lbl_97;
}
lbl_116:
{
obj* x_174; unsigned char x_175; 
x_174 = lean::mk_nat_obj(102u);
x_175 = lean::nat_dec_lt(x_174, x_113);
lean::dec(x_113);
if (x_175 == 0)
{
obj* x_177; unsigned char x_178; 
x_177 = lean::mk_nat_obj(57343u);
x_178 = lean::nat_dec_lt(x_177, x_174);
lean::dec(x_177);
if (x_178 == 0)
{
obj* x_181; obj* x_182; unsigned char x_183; 
lean::dec(x_174);
x_181 = lean::mk_nat_obj(0u);
x_182 = lean::box_uint32(x_107);
x_183 = lean::nat_dec_le(x_182, x_181);
lean::dec(x_181);
lean::dec(x_182);
if (x_183 == 0)
{
obj* x_186; 
x_186 = lean::box(0);
x_108 = x_186;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_187; 
x_187 = lean::box(0);
x_108 = x_187;
goto lbl_109;
}
else
{
obj* x_188; 
x_188 = lean::box(0);
x_110 = x_188;
goto lbl_111;
}
}
}
else
{
obj* x_189; unsigned char x_190; 
x_189 = lean::mk_nat_obj(1114112u);
x_190 = lean::nat_dec_lt(x_174, x_189);
lean::dec(x_189);
if (x_190 == 0)
{
obj* x_193; obj* x_194; unsigned char x_195; 
lean::dec(x_174);
x_193 = lean::mk_nat_obj(0u);
x_194 = lean::box_uint32(x_107);
x_195 = lean::nat_dec_le(x_194, x_193);
lean::dec(x_193);
lean::dec(x_194);
if (x_195 == 0)
{
obj* x_198; 
x_198 = lean::box(0);
x_108 = x_198;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_199; 
x_199 = lean::box(0);
x_108 = x_199;
goto lbl_109;
}
else
{
obj* x_200; 
x_200 = lean::box(0);
x_110 = x_200;
goto lbl_111;
}
}
}
else
{
obj* x_201; unsigned char x_202; 
x_201 = lean::box_uint32(x_107);
x_202 = lean::nat_dec_le(x_201, x_174);
lean::dec(x_174);
lean::dec(x_201);
if (x_202 == 0)
{
obj* x_205; 
x_205 = lean::box(0);
x_108 = x_205;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_206; 
x_206 = lean::box(0);
x_108 = x_206;
goto lbl_109;
}
else
{
obj* x_207; 
x_207 = lean::box(0);
x_110 = x_207;
goto lbl_111;
}
}
}
}
}
else
{
obj* x_208; unsigned char x_209; 
x_208 = lean::box_uint32(x_107);
x_209 = lean::nat_dec_le(x_208, x_174);
lean::dec(x_174);
lean::dec(x_208);
if (x_209 == 0)
{
obj* x_212; 
x_212 = lean::box(0);
x_108 = x_212;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_213; 
x_213 = lean::box(0);
x_108 = x_213;
goto lbl_109;
}
else
{
obj* x_214; 
x_214 = lean::box(0);
x_110 = x_214;
goto lbl_111;
}
}
}
}
}
lbl_97:
{
obj* x_215; obj* x_217; 
x_215 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_215);
x_217 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_215, x_96);
if (lean::obj_tag(x_217) == 0)
{
obj* x_218; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_226; unsigned char x_227; 
x_218 = lean::cnstr_get(x_217, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_217, 2);
lean::inc(x_222);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_224 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 lean::cnstr_release(x_217, 1);
 lean::cnstr_release(x_217, 2);
 x_224 = x_217;
}
x_225 = lean::mk_nat_obj(97u);
x_226 = lean::mk_nat_obj(55296u);
x_227 = lean::nat_dec_lt(x_225, x_226);
lean::dec(x_226);
if (x_227 == 0)
{
obj* x_229; unsigned char x_230; 
x_229 = lean::mk_nat_obj(57343u);
x_230 = lean::nat_dec_lt(x_229, x_225);
lean::dec(x_229);
if (x_230 == 0)
{
obj* x_233; obj* x_234; obj* x_237; obj* x_238; obj* x_242; obj* x_243; 
lean::dec(x_225);
x_233 = lean::mk_nat_obj(0u);
x_234 = lean::nat_sub(x_218, x_233);
lean::dec(x_233);
lean::dec(x_218);
x_237 = lean::mk_nat_obj(10u);
x_238 = lean::nat_add(x_237, x_234);
lean::dec(x_234);
lean::dec(x_237);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_242 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_242 = x_224;
}
lean::cnstr_set(x_242, 0, x_238);
lean::cnstr_set(x_242, 1, x_220);
lean::cnstr_set(x_242, 2, x_215);
x_243 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_242);
if (lean::obj_tag(x_243) == 0)
{
obj* x_245; obj* x_246; obj* x_248; 
lean::dec(x_0);
x_245 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_243);
x_246 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_246);
x_248 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_245, x_246);
return x_248;
}
else
{
obj* x_249; unsigned char x_251; 
x_249 = lean::cnstr_get(x_243, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get_scalar<unsigned char>(x_243, sizeof(void*)*1);
x_91 = x_243;
x_92 = x_249;
x_93 = x_251;
goto lbl_94;
}
}
else
{
obj* x_252; unsigned char x_253; 
x_252 = lean::mk_nat_obj(1114112u);
x_253 = lean::nat_dec_lt(x_225, x_252);
lean::dec(x_252);
if (x_253 == 0)
{
obj* x_256; obj* x_257; obj* x_260; obj* x_261; obj* x_265; obj* x_266; 
lean::dec(x_225);
x_256 = lean::mk_nat_obj(0u);
x_257 = lean::nat_sub(x_218, x_256);
lean::dec(x_256);
lean::dec(x_218);
x_260 = lean::mk_nat_obj(10u);
x_261 = lean::nat_add(x_260, x_257);
lean::dec(x_257);
lean::dec(x_260);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_265 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_265 = x_224;
}
lean::cnstr_set(x_265, 0, x_261);
lean::cnstr_set(x_265, 1, x_220);
lean::cnstr_set(x_265, 2, x_215);
x_266 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_265);
if (lean::obj_tag(x_266) == 0)
{
obj* x_268; obj* x_269; obj* x_271; 
lean::dec(x_0);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_266);
x_269 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_269);
x_271 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_268, x_269);
return x_271;
}
else
{
obj* x_272; unsigned char x_274; 
x_272 = lean::cnstr_get(x_266, 0);
lean::inc(x_272);
x_274 = lean::cnstr_get_scalar<unsigned char>(x_266, sizeof(void*)*1);
x_91 = x_266;
x_92 = x_272;
x_93 = x_274;
goto lbl_94;
}
}
else
{
obj* x_275; obj* x_278; obj* x_279; obj* x_283; obj* x_284; 
x_275 = lean::nat_sub(x_218, x_225);
lean::dec(x_225);
lean::dec(x_218);
x_278 = lean::mk_nat_obj(10u);
x_279 = lean::nat_add(x_278, x_275);
lean::dec(x_275);
lean::dec(x_278);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_283 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_283 = x_224;
}
lean::cnstr_set(x_283, 0, x_279);
lean::cnstr_set(x_283, 1, x_220);
lean::cnstr_set(x_283, 2, x_215);
x_284 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_283);
if (lean::obj_tag(x_284) == 0)
{
obj* x_286; obj* x_287; obj* x_289; 
lean::dec(x_0);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_284);
x_287 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_287);
x_289 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_286, x_287);
return x_289;
}
else
{
obj* x_290; unsigned char x_292; 
x_290 = lean::cnstr_get(x_284, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get_scalar<unsigned char>(x_284, sizeof(void*)*1);
x_91 = x_284;
x_92 = x_290;
x_93 = x_292;
goto lbl_94;
}
}
}
}
else
{
obj* x_293; obj* x_296; obj* x_297; obj* x_301; obj* x_302; 
x_293 = lean::nat_sub(x_218, x_225);
lean::dec(x_225);
lean::dec(x_218);
x_296 = lean::mk_nat_obj(10u);
x_297 = lean::nat_add(x_296, x_293);
lean::dec(x_293);
lean::dec(x_296);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_301 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_301 = x_224;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set(x_301, 1, x_220);
lean::cnstr_set(x_301, 2, x_215);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_301);
if (lean::obj_tag(x_302) == 0)
{
obj* x_304; obj* x_305; obj* x_307; 
lean::dec(x_0);
x_304 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_302);
x_305 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_305);
x_307 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_304, x_305);
return x_307;
}
else
{
obj* x_308; unsigned char x_310; 
x_308 = lean::cnstr_get(x_302, 0);
lean::inc(x_308);
x_310 = lean::cnstr_get_scalar<unsigned char>(x_302, sizeof(void*)*1);
x_91 = x_302;
x_92 = x_308;
x_93 = x_310;
goto lbl_94;
}
}
}
else
{
obj* x_311; unsigned char x_313; obj* x_314; obj* x_316; obj* x_317; 
x_311 = lean::cnstr_get(x_217, 0);
lean::inc(x_311);
x_313 = lean::cnstr_get_scalar<unsigned char>(x_217, sizeof(void*)*1);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_314 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_314 = x_217;
}
lean::inc(x_311);
if (lean::is_scalar(x_314)) {
 x_316 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_316 = x_314;
}
lean::cnstr_set(x_316, 0, x_311);
lean::cnstr_set_scalar(x_316, sizeof(void*)*1, x_313);
x_317 = x_316;
x_91 = x_317;
x_92 = x_311;
x_93 = x_313;
goto lbl_94;
}
}
}
else
{
obj* x_320; obj* x_322; 
lean::dec(x_0);
lean::dec(x_2);
x_320 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_320);
x_322 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_320);
return x_322;
}
lbl_94:
{
if (x_93 == 0)
{
obj* x_324; unsigned char x_326; 
lean::dec(x_91);
x_326 = lean::string_iterator_has_next(x_0);
if (x_326 == 0)
{
obj* x_327; obj* x_328; obj* x_329; obj* x_333; 
x_327 = lean::box(0);
x_328 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_329 = l_mjoin___rarg___closed__1;
lean::inc(x_327);
lean::inc(x_329);
lean::inc(x_328);
x_333 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_328, x_329, x_327, x_327, x_0);
x_324 = x_333;
goto lbl_325;
}
else
{
unsigned x_334; obj* x_335; obj* x_337; obj* x_339; obj* x_340; unsigned char x_341; unsigned char x_342; 
x_334 = lean::string_iterator_curr(x_0);
x_339 = lean::mk_nat_obj(65u);
x_340 = lean::mk_nat_obj(55296u);
x_341 = lean::nat_dec_lt(x_339, x_340);
if (x_341 == 0)
{
obj* x_344; unsigned char x_345; 
x_344 = lean::mk_nat_obj(57343u);
x_345 = lean::nat_dec_lt(x_344, x_339);
lean::dec(x_344);
if (x_345 == 0)
{
obj* x_348; obj* x_349; unsigned char x_350; 
lean::dec(x_339);
x_348 = lean::mk_nat_obj(0u);
x_349 = lean::box_uint32(x_334);
x_350 = lean::nat_dec_le(x_348, x_349);
lean::dec(x_349);
lean::dec(x_348);
if (x_350 == 0)
{
obj* x_354; 
lean::dec(x_340);
x_354 = lean::box(0);
x_335 = x_354;
goto lbl_336;
}
else
{
unsigned char x_355; 
x_355 = 1;
x_342 = x_355;
goto lbl_343;
}
}
else
{
obj* x_356; unsigned char x_357; 
x_356 = lean::mk_nat_obj(1114112u);
x_357 = lean::nat_dec_lt(x_339, x_356);
lean::dec(x_356);
if (x_357 == 0)
{
obj* x_360; obj* x_361; unsigned char x_362; 
lean::dec(x_339);
x_360 = lean::mk_nat_obj(0u);
x_361 = lean::box_uint32(x_334);
x_362 = lean::nat_dec_le(x_360, x_361);
lean::dec(x_361);
lean::dec(x_360);
if (x_362 == 0)
{
obj* x_366; 
lean::dec(x_340);
x_366 = lean::box(0);
x_335 = x_366;
goto lbl_336;
}
else
{
unsigned char x_367; 
x_367 = 1;
x_342 = x_367;
goto lbl_343;
}
}
else
{
obj* x_368; unsigned char x_369; 
x_368 = lean::box_uint32(x_334);
x_369 = lean::nat_dec_le(x_339, x_368);
lean::dec(x_368);
lean::dec(x_339);
if (x_369 == 0)
{
obj* x_373; 
lean::dec(x_340);
x_373 = lean::box(0);
x_335 = x_373;
goto lbl_336;
}
else
{
unsigned char x_374; 
x_374 = 1;
x_342 = x_374;
goto lbl_343;
}
}
}
}
else
{
obj* x_375; unsigned char x_376; 
x_375 = lean::box_uint32(x_334);
x_376 = lean::nat_dec_le(x_339, x_375);
lean::dec(x_375);
lean::dec(x_339);
if (x_376 == 0)
{
obj* x_380; 
lean::dec(x_340);
x_380 = lean::box(0);
x_335 = x_380;
goto lbl_336;
}
else
{
unsigned char x_381; 
x_381 = 1;
x_342 = x_381;
goto lbl_343;
}
}
lbl_336:
{
obj* x_383; obj* x_384; obj* x_386; obj* x_388; obj* x_389; obj* x_390; obj* x_393; 
lean::dec(x_335);
x_383 = l_char_quote__core(x_334);
x_384 = l_char_has__repr___closed__1;
lean::inc(x_384);
x_386 = lean::string_append(x_384, x_383);
lean::dec(x_383);
x_388 = lean::string_append(x_386, x_384);
x_389 = lean::box(0);
x_390 = l_mjoin___rarg___closed__1;
lean::inc(x_389);
lean::inc(x_390);
x_393 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_388, x_390, x_389, x_389, x_0);
x_324 = x_393;
goto lbl_325;
}
lbl_338:
{
obj* x_395; obj* x_396; obj* x_397; obj* x_398; 
lean::dec(x_337);
x_395 = lean::string_iterator_next(x_0);
x_396 = lean::box(0);
x_397 = lean::box_uint32(x_334);
x_398 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_398, 0, x_397);
lean::cnstr_set(x_398, 1, x_395);
lean::cnstr_set(x_398, 2, x_396);
x_324 = x_398;
goto lbl_325;
}
lbl_343:
{
obj* x_399; unsigned char x_400; 
x_399 = lean::mk_nat_obj(70u);
x_400 = lean::nat_dec_lt(x_399, x_340);
lean::dec(x_340);
if (x_400 == 0)
{
obj* x_402; unsigned char x_403; 
x_402 = lean::mk_nat_obj(57343u);
x_403 = lean::nat_dec_lt(x_402, x_399);
lean::dec(x_402);
if (x_403 == 0)
{
obj* x_406; obj* x_407; unsigned char x_408; 
lean::dec(x_399);
x_406 = lean::mk_nat_obj(0u);
x_407 = lean::box_uint32(x_334);
x_408 = lean::nat_dec_le(x_407, x_406);
lean::dec(x_406);
lean::dec(x_407);
if (x_408 == 0)
{
obj* x_411; 
x_411 = lean::box(0);
x_335 = x_411;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_412; 
x_412 = lean::box(0);
x_335 = x_412;
goto lbl_336;
}
else
{
obj* x_413; 
x_413 = lean::box(0);
x_337 = x_413;
goto lbl_338;
}
}
}
else
{
obj* x_414; unsigned char x_415; 
x_414 = lean::mk_nat_obj(1114112u);
x_415 = lean::nat_dec_lt(x_399, x_414);
lean::dec(x_414);
if (x_415 == 0)
{
obj* x_418; obj* x_419; unsigned char x_420; 
lean::dec(x_399);
x_418 = lean::mk_nat_obj(0u);
x_419 = lean::box_uint32(x_334);
x_420 = lean::nat_dec_le(x_419, x_418);
lean::dec(x_418);
lean::dec(x_419);
if (x_420 == 0)
{
obj* x_423; 
x_423 = lean::box(0);
x_335 = x_423;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_424; 
x_424 = lean::box(0);
x_335 = x_424;
goto lbl_336;
}
else
{
obj* x_425; 
x_425 = lean::box(0);
x_337 = x_425;
goto lbl_338;
}
}
}
else
{
obj* x_426; unsigned char x_427; 
x_426 = lean::box_uint32(x_334);
x_427 = lean::nat_dec_le(x_426, x_399);
lean::dec(x_399);
lean::dec(x_426);
if (x_427 == 0)
{
obj* x_430; 
x_430 = lean::box(0);
x_335 = x_430;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_431; 
x_431 = lean::box(0);
x_335 = x_431;
goto lbl_336;
}
else
{
obj* x_432; 
x_432 = lean::box(0);
x_337 = x_432;
goto lbl_338;
}
}
}
}
}
else
{
obj* x_433; unsigned char x_434; 
x_433 = lean::box_uint32(x_334);
x_434 = lean::nat_dec_le(x_433, x_399);
lean::dec(x_399);
lean::dec(x_433);
if (x_434 == 0)
{
obj* x_437; 
x_437 = lean::box(0);
x_335 = x_437;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_438; 
x_438 = lean::box(0);
x_335 = x_438;
goto lbl_336;
}
else
{
obj* x_439; 
x_439 = lean::box(0);
x_337 = x_439;
goto lbl_338;
}
}
}
}
}
lbl_325:
{
obj* x_440; obj* x_442; 
x_440 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_440);
x_442 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_440, x_324);
if (lean::obj_tag(x_442) == 0)
{
obj* x_443; obj* x_445; obj* x_447; obj* x_449; obj* x_450; obj* x_451; unsigned char x_452; 
x_443 = lean::cnstr_get(x_442, 0);
lean::inc(x_443);
x_445 = lean::cnstr_get(x_442, 1);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_442, 2);
lean::inc(x_447);
if (lean::is_shared(x_442)) {
 lean::dec(x_442);
 x_449 = lean::box(0);
} else {
 lean::cnstr_release(x_442, 0);
 lean::cnstr_release(x_442, 1);
 lean::cnstr_release(x_442, 2);
 x_449 = x_442;
}
x_450 = lean::mk_nat_obj(65u);
x_451 = lean::mk_nat_obj(55296u);
x_452 = lean::nat_dec_lt(x_450, x_451);
lean::dec(x_451);
if (x_452 == 0)
{
obj* x_454; unsigned char x_455; 
x_454 = lean::mk_nat_obj(57343u);
x_455 = lean::nat_dec_lt(x_454, x_450);
lean::dec(x_454);
if (x_455 == 0)
{
obj* x_458; obj* x_459; obj* x_462; obj* x_463; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_473; 
lean::dec(x_450);
x_458 = lean::mk_nat_obj(0u);
x_459 = lean::nat_sub(x_443, x_458);
lean::dec(x_458);
lean::dec(x_443);
x_462 = lean::mk_nat_obj(10u);
x_463 = lean::nat_add(x_462, x_459);
lean::dec(x_459);
lean::dec(x_462);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_467 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_467 = x_449;
}
lean::cnstr_set(x_467, 0, x_463);
lean::cnstr_set(x_467, 1, x_445);
lean::cnstr_set(x_467, 2, x_440);
x_468 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_467);
x_469 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_468);
x_470 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_469);
x_471 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_471);
x_473 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_470, x_471);
return x_473;
}
else
{
obj* x_474; unsigned char x_475; 
x_474 = lean::mk_nat_obj(1114112u);
x_475 = lean::nat_dec_lt(x_450, x_474);
lean::dec(x_474);
if (x_475 == 0)
{
obj* x_478; obj* x_479; obj* x_482; obj* x_483; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_493; 
lean::dec(x_450);
x_478 = lean::mk_nat_obj(0u);
x_479 = lean::nat_sub(x_443, x_478);
lean::dec(x_478);
lean::dec(x_443);
x_482 = lean::mk_nat_obj(10u);
x_483 = lean::nat_add(x_482, x_479);
lean::dec(x_479);
lean::dec(x_482);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_487 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_487 = x_449;
}
lean::cnstr_set(x_487, 0, x_483);
lean::cnstr_set(x_487, 1, x_445);
lean::cnstr_set(x_487, 2, x_440);
x_488 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_487);
x_489 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_488);
x_490 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_489);
x_491 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_491);
x_493 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_490, x_491);
return x_493;
}
else
{
obj* x_494; obj* x_497; obj* x_498; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_508; 
x_494 = lean::nat_sub(x_443, x_450);
lean::dec(x_450);
lean::dec(x_443);
x_497 = lean::mk_nat_obj(10u);
x_498 = lean::nat_add(x_497, x_494);
lean::dec(x_494);
lean::dec(x_497);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_502 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_502 = x_449;
}
lean::cnstr_set(x_502, 0, x_498);
lean::cnstr_set(x_502, 1, x_445);
lean::cnstr_set(x_502, 2, x_440);
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_502);
x_504 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_503);
x_505 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_504);
x_506 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_506);
x_508 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_505, x_506);
return x_508;
}
}
}
else
{
obj* x_509; obj* x_512; obj* x_513; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_523; 
x_509 = lean::nat_sub(x_443, x_450);
lean::dec(x_450);
lean::dec(x_443);
x_512 = lean::mk_nat_obj(10u);
x_513 = lean::nat_add(x_512, x_509);
lean::dec(x_509);
lean::dec(x_512);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_517 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_517 = x_449;
}
lean::cnstr_set(x_517, 0, x_513);
lean::cnstr_set(x_517, 1, x_445);
lean::cnstr_set(x_517, 2, x_440);
x_518 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_517);
x_519 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_518);
x_520 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_519);
x_521 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_521);
x_523 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_520, x_521);
return x_523;
}
}
else
{
obj* x_524; unsigned char x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; obj* x_531; obj* x_532; obj* x_534; 
x_524 = lean::cnstr_get(x_442, 0);
lean::inc(x_524);
x_526 = lean::cnstr_get_scalar<unsigned char>(x_442, sizeof(void*)*1);
if (lean::is_shared(x_442)) {
 lean::dec(x_442);
 x_527 = lean::box(0);
} else {
 lean::cnstr_release(x_442, 0);
 x_527 = x_442;
}
if (lean::is_scalar(x_527)) {
 x_528 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_528 = x_527;
}
lean::cnstr_set(x_528, 0, x_524);
lean::cnstr_set_scalar(x_528, sizeof(void*)*1, x_526);
x_529 = x_528;
x_530 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_529);
x_531 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_530);
x_532 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_532);
x_534 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_531, x_532);
return x_534;
}
}
}
else
{
obj* x_537; obj* x_538; obj* x_540; 
lean::dec(x_0);
lean::dec(x_92);
x_537 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_91);
x_538 = l_lean_parser_parse__hex__digit___at___private_1496486805__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_538);
x_540 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_537, x_538);
return x_540;
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
obj* x_1; obj* x_2; unsigned char x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (x_3 == 0)
{
unsigned x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_17; 
x_6 = lean::string_iterator_curr(x_0);
x_7 = l_char_quote__core(x_6);
x_8 = l_char_has__repr___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = lean::string_append(x_10, x_8);
x_13 = lean::box(0);
x_14 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
lean::inc(x_13);
lean::inc(x_14);
x_17 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_12, x_14, x_13, x_13, x_0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_22; 
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_17, 2);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_22);
lean::dec(x_18);
lean::dec(x_20);
return x_17;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_17);
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_30 = x_22;
}
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_28);
if (lean::is_scalar(x_30)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_30;
}
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_18);
lean::cnstr_set(x_35, 1, x_20);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
}
}
else
{
obj* x_36; unsigned char x_38; 
x_36 = lean::cnstr_get(x_17, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<unsigned char>(x_17, sizeof(void*)*1);
if (x_38 == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_17);
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_36, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_36, 2);
lean::inc(x_44);
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_48, 0, x_46);
lean::closure_set(x_48, 1, x_44);
x_49 = lean::cnstr_get(x_36, 3);
lean::inc(x_49);
lean::dec(x_36);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_40);
lean::cnstr_set(x_52, 1, x_42);
lean::cnstr_set(x_52, 2, x_48);
lean::cnstr_set(x_52, 3, x_49);
x_53 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_38);
x_54 = x_53;
return x_54;
}
else
{
lean::dec(x_36);
return x_17;
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_59; 
x_56 = lean::box(0);
x_57 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_0);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
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
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; unsigned char x_11; obj* x_14; unsigned x_15; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
x_9 = lean::mk_nat_obj(95u);
x_10 = lean::mk_nat_obj(55296u);
x_11 = lean::nat_dec_lt(x_9, x_10);
lean::dec(x_10);
lean::inc(x_2);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_1496486805__parse__mangled__string__aux___main___spec__6(x_2);
if (x_11 == 0)
{
obj* x_17; unsigned char x_18; 
x_17 = lean::mk_nat_obj(57343u);
x_18 = lean::nat_dec_lt(x_17, x_9);
lean::dec(x_17);
if (x_18 == 0)
{
unsigned x_20; 
x_20 = lean::unbox_uint32(x_3);
x_15 = x_20;
goto lbl_16;
}
else
{
obj* x_21; unsigned char x_22; 
x_21 = lean::mk_nat_obj(1114112u);
x_22 = lean::nat_dec_lt(x_9, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
unsigned x_24; 
x_24 = lean::unbox_uint32(x_3);
x_15 = x_24;
goto lbl_16;
}
else
{
unsigned x_25; 
x_25 = lean::unbox_uint32(x_9);
x_15 = x_25;
goto lbl_16;
}
}
}
else
{
unsigned x_26; 
x_26 = lean::unbox_uint32(x_9);
x_15 = x_26;
goto lbl_16;
}
lbl_16:
{
obj* x_27; 
if (lean::obj_tag(x_14) == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_29 = lean::cnstr_get(x_14, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_14, 2);
lean::inc(x_31);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_33 = x_14;
}
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_34);
lean::inc(x_1);
if (lean::is_scalar(x_33)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_33;
}
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 2, x_34);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_37);
x_27 = x_38;
goto lbl_28;
}
else
{
obj* x_39; unsigned char x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_14, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<unsigned char>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_42 = x_14;
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
x_27 = x_44;
goto lbl_28;
}
lbl_28:
{
if (lean::obj_tag(x_27) == 0)
{
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_27;
}
else
{
obj* x_50; unsigned char x_52; obj* x_53; obj* x_54; unsigned char x_55; 
x_50 = lean::cnstr_get(x_27, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<unsigned char>(x_27, sizeof(void*)*1);
if (x_52 == 0)
{
obj* x_58; obj* x_59; obj* x_63; 
lean::dec(x_27);
x_58 = l___private_1205956357__name_mangle__aux___main___closed__1;
x_59 = l___private_4217055689__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_59);
lean::inc(x_58);
x_63 = l_lean_parser_monad__parsec_str__core___at___private_1496486805__parse__mangled__string__aux___main___spec__1(x_58, x_59, x_2);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 2);
lean::inc(x_66);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 lean::cnstr_release(x_63, 2);
 x_68 = x_63;
}
x_69 = l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(x_64);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_74; unsigned x_77; 
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 2);
lean::inc(x_74);
lean::dec(x_69);
if (x_11 == 0)
{
obj* x_79; unsigned char x_80; 
x_79 = lean::mk_nat_obj(57343u);
x_80 = lean::nat_dec_lt(x_79, x_9);
lean::dec(x_79);
if (x_80 == 0)
{
unsigned x_83; 
lean::dec(x_9);
x_83 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_77 = x_83;
goto lbl_78;
}
else
{
obj* x_85; unsigned char x_86; 
x_85 = lean::mk_nat_obj(1114112u);
x_86 = lean::nat_dec_lt(x_9, x_85);
lean::dec(x_85);
if (x_86 == 0)
{
unsigned x_89; 
lean::dec(x_9);
x_89 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_77 = x_89;
goto lbl_78;
}
else
{
unsigned x_92; 
lean::dec(x_3);
x_92 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_77 = x_92;
goto lbl_78;
}
}
}
else
{
unsigned x_95; 
lean::dec(x_3);
x_95 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_77 = x_95;
goto lbl_78;
}
lbl_78:
{
obj* x_97; 
x_97 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_77, x_72);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_103; 
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 2);
lean::inc(x_100);
lean::dec(x_97);
x_103 = l_lean_parser_monad__parsec_take___at___private_4217055689__parse__mangled__name__aux___main___spec__18(x_70, x_98);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_106; obj* x_108; obj* x_111; obj* x_112; obj* x_114; obj* x_115; 
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_103, 2);
lean::inc(x_108);
lean::dec(x_103);
x_111 = l_lean_string_demangle(x_104);
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_112);
if (lean::is_scalar(x_68)) {
 x_114 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_114 = x_68;
}
lean::cnstr_set(x_114, 0, x_111);
lean::cnstr_set(x_114, 1, x_106);
lean::cnstr_set(x_114, 2, x_112);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_108, x_114);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_118; obj* x_120; 
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 2);
lean::inc(x_120);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_116);
x_124 = l_match__failed___at___private_4217055689__parse__mangled__name__aux___main___spec__19(x_118);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_120, x_124);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_132; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_128);
return x_132;
}
else
{
obj* x_133; unsigned char x_135; 
x_133 = lean::cnstr_get(x_128, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<unsigned char>(x_128, sizeof(void*)*1);
x_53 = x_128;
x_54 = x_133;
x_55 = x_135;
goto lbl_56;
}
}
else
{
obj* x_136; obj* x_140; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_136 = lean::cnstr_get(x_116, 0);
lean::inc(x_136);
lean::dec(x_116);
lean::inc(x_1);
x_140 = lean::name_mk_string(x_1, x_136);
lean::inc(x_6);
x_142 = l___private_4217055689__parse__mangled__name__aux___main(x_6, x_140, x_118);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_120, x_142);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_145);
if (lean::obj_tag(x_146) == 0)
{
obj* x_150; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_150 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_146);
return x_150;
}
else
{
obj* x_151; unsigned char x_153; 
x_151 = lean::cnstr_get(x_146, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get_scalar<unsigned char>(x_146, sizeof(void*)*1);
x_53 = x_146;
x_54 = x_151;
x_55 = x_153;
goto lbl_56;
}
}
}
else
{
obj* x_154; unsigned char x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_154 = lean::cnstr_get(x_115, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get_scalar<unsigned char>(x_115, sizeof(void*)*1);
if (lean::is_shared(x_115)) {
 lean::dec(x_115);
 x_157 = lean::box(0);
} else {
 lean::cnstr_release(x_115, 0);
 x_157 = x_115;
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_154);
lean::cnstr_set_scalar(x_158, sizeof(void*)*1, x_156);
x_159 = x_158;
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_160);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_161);
if (lean::obj_tag(x_162) == 0)
{
obj* x_166; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_162);
return x_166;
}
else
{
obj* x_167; unsigned char x_169; 
x_167 = lean::cnstr_get(x_162, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get_scalar<unsigned char>(x_162, sizeof(void*)*1);
x_53 = x_162;
x_54 = x_167;
x_55 = x_169;
goto lbl_56;
}
}
}
else
{
obj* x_171; unsigned char x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_68);
x_171 = lean::cnstr_get(x_103, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get_scalar<unsigned char>(x_103, sizeof(void*)*1);
if (lean::is_shared(x_103)) {
 lean::dec(x_103);
 x_174 = lean::box(0);
} else {
 lean::cnstr_release(x_103, 0);
 x_174 = x_103;
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_171);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_173);
x_176 = x_175;
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_176);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_177);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_178);
if (lean::obj_tag(x_179) == 0)
{
obj* x_183; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_183 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_179);
return x_183;
}
else
{
obj* x_184; unsigned char x_186; 
x_184 = lean::cnstr_get(x_179, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get_scalar<unsigned char>(x_179, sizeof(void*)*1);
x_53 = x_179;
x_54 = x_184;
x_55 = x_186;
goto lbl_56;
}
}
}
else
{
obj* x_189; unsigned char x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_68);
lean::dec(x_70);
x_189 = lean::cnstr_get(x_97, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get_scalar<unsigned char>(x_97, sizeof(void*)*1);
if (lean::is_shared(x_97)) {
 lean::dec(x_97);
 x_192 = lean::box(0);
} else {
 lean::cnstr_release(x_97, 0);
 x_192 = x_97;
}
if (lean::is_scalar(x_192)) {
 x_193 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_193 = x_192;
}
lean::cnstr_set(x_193, 0, x_189);
lean::cnstr_set_scalar(x_193, sizeof(void*)*1, x_191);
x_194 = x_193;
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_195);
if (lean::obj_tag(x_196) == 0)
{
obj* x_200; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_200 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_196);
return x_200;
}
else
{
obj* x_201; unsigned char x_203; 
x_201 = lean::cnstr_get(x_196, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get_scalar<unsigned char>(x_196, sizeof(void*)*1);
x_53 = x_196;
x_54 = x_201;
x_55 = x_203;
goto lbl_56;
}
}
}
}
else
{
obj* x_207; unsigned char x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_68);
x_207 = lean::cnstr_get(x_69, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get_scalar<unsigned char>(x_69, sizeof(void*)*1);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_210 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_210 = x_69;
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_207);
lean::cnstr_set_scalar(x_211, sizeof(void*)*1, x_209);
x_212 = x_211;
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_212);
if (lean::obj_tag(x_213) == 0)
{
obj* x_217; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_213);
return x_217;
}
else
{
obj* x_218; unsigned char x_220; 
x_218 = lean::cnstr_get(x_213, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<unsigned char>(x_213, sizeof(void*)*1);
x_53 = x_213;
x_54 = x_218;
x_55 = x_220;
goto lbl_56;
}
}
}
else
{
obj* x_223; unsigned char x_225; obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_9);
lean::dec(x_3);
x_223 = lean::cnstr_get(x_63, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get_scalar<unsigned char>(x_63, sizeof(void*)*1);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_226 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_226 = x_63;
}
lean::inc(x_223);
if (lean::is_scalar(x_226)) {
 x_228 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_228 = x_226;
}
lean::cnstr_set(x_228, 0, x_223);
lean::cnstr_set_scalar(x_228, sizeof(void*)*1, x_225);
x_229 = x_228;
x_53 = x_229;
x_54 = x_223;
x_55 = x_225;
goto lbl_56;
}
}
else
{
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_50);
return x_27;
}
lbl_56:
{
if (x_55 == 0)
{
obj* x_237; 
lean::dec(x_53);
x_237 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_15, x_2);
if (lean::obj_tag(x_237) == 0)
{
obj* x_238; obj* x_240; obj* x_243; 
x_238 = lean::cnstr_get(x_237, 1);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 2);
lean::inc(x_240);
lean::dec(x_237);
x_243 = l_lean_parser_monad__parsec_num___at___private_4217055689__parse__mangled__name__aux___main___spec__2(x_238);
if (lean::obj_tag(x_243) == 0)
{
obj* x_244; obj* x_246; obj* x_248; obj* x_251; 
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get(x_243, 1);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_243, 2);
lean::inc(x_248);
lean::dec(x_243);
x_251 = l_lean_parser_monad__parsec_ch___at___private_4217055689__parse__mangled__name__aux___main___spec__1(x_15, x_246);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_254; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
x_252 = lean::cnstr_get(x_251, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 2);
lean::inc(x_254);
lean::dec(x_251);
x_257 = lean::name_mk_numeral(x_1, x_244);
x_258 = l___private_4217055689__parse__mangled__name__aux___main(x_6, x_257, x_252);
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_254, x_258);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_259);
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_240, x_260);
x_262 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_261);
x_263 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_262);
return x_263;
}
else
{
obj* x_267; unsigned char x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_244);
lean::dec(x_1);
lean::dec(x_6);
x_267 = lean::cnstr_get(x_251, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get_scalar<unsigned char>(x_251, sizeof(void*)*1);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_270 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_270 = x_251;
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_267);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_269);
x_272 = x_271;
x_273 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_272);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_240, x_273);
x_275 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_274);
x_276 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_275);
return x_276;
}
}
else
{
obj* x_279; unsigned char x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_1);
lean::dec(x_6);
x_279 = lean::cnstr_get(x_243, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get_scalar<unsigned char>(x_243, sizeof(void*)*1);
if (lean::is_shared(x_243)) {
 lean::dec(x_243);
 x_282 = lean::box(0);
} else {
 lean::cnstr_release(x_243, 0);
 x_282 = x_243;
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_279);
lean::cnstr_set_scalar(x_283, sizeof(void*)*1, x_281);
x_284 = x_283;
x_285 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_240, x_284);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_285);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_286);
return x_287;
}
}
else
{
obj* x_290; unsigned char x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_1);
lean::dec(x_6);
x_290 = lean::cnstr_get(x_237, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get_scalar<unsigned char>(x_237, sizeof(void*)*1);
if (lean::is_shared(x_237)) {
 lean::dec(x_237);
 x_293 = lean::box(0);
} else {
 lean::cnstr_release(x_237, 0);
 x_293 = x_237;
}
if (lean::is_scalar(x_293)) {
 x_294 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_294 = x_293;
}
lean::cnstr_set(x_294, 0, x_290);
lean::cnstr_set_scalar(x_294, sizeof(void*)*1, x_292);
x_295 = x_294;
x_296 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_295);
x_297 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_296);
return x_297;
}
}
else
{
obj* x_302; 
lean::dec(x_54);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
x_302 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_53);
return x_302;
}
}
}
}
}
}
else
{
obj* x_305; obj* x_307; 
lean::dec(x_3);
lean::dec(x_0);
x_305 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_305);
x_307 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_307, 0, x_1);
lean::cnstr_set(x_307, 1, x_2);
lean::cnstr_set(x_307, 2, x_305);
return x_307;
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
unsigned x_46; obj* x_47; obj* x_48; unsigned char x_49; 
x_46 = lean::string_iterator_curr(x_1);
x_47 = lean::box_uint32(x_46);
x_48 = lean::box_uint32(x_0);
x_49 = lean::nat_dec_eq(x_47, x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_47);
x_52 = l_char_quote__core(x_46);
x_53 = l_char_has__repr___closed__1;
lean::inc(x_53);
x_55 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_57 = lean::string_append(x_55, x_53);
x_58 = lean::box(0);
x_59 = l_mjoin___rarg___closed__1;
lean::inc(x_58);
lean::inc(x_59);
x_62 = l_lean_parser_monad__parsec_error___at___private_1496486805__parse__mangled__string__aux___main___spec__3___rarg(x_57, x_59, x_58, x_58, x_1);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
lean::dec(x_65);
lean::dec(x_63);
lean::dec(x_67);
return x_62;
}
else
{
obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_62);
x_73 = lean::cnstr_get(x_67, 0);
lean::inc(x_73);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_75 = x_67;
}
lean::inc(x_59);
x_77 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_77, 0, x_59);
lean::closure_set(x_77, 1, x_73);
if (lean::is_scalar(x_75)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_75;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_63);
lean::cnstr_set(x_79, 1, x_65);
lean::cnstr_set(x_79, 2, x_78);
return x_79;
}
}
else
{
obj* x_80; unsigned char x_82; 
x_80 = lean::cnstr_get(x_62, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<unsigned char>(x_62, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_62);
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_80, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_80, 2);
lean::inc(x_88);
lean::inc(x_59);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_91, 0, x_59);
lean::closure_set(x_91, 1, x_88);
x_92 = lean::cnstr_get(x_80, 3);
lean::inc(x_92);
lean::dec(x_80);
x_95 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_95, 0, x_84);
lean::cnstr_set(x_95, 1, x_86);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_92);
x_96 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_82);
x_97 = x_96;
return x_97;
}
else
{
lean::dec(x_80);
return x_62;
}
}
}
else
{
obj* x_99; obj* x_100; obj* x_101; 
x_99 = lean::string_iterator_next(x_1);
x_100 = lean::box(0);
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_47);
lean::cnstr_set(x_101, 1, x_99);
lean::cnstr_set(x_101, 2, x_100);
return x_101;
}
}
}
}
obj* l___private_31565857__take__while__aux___main___at___private_4217055689__parse__mangled__name__aux___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
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
obj* x_2; unsigned char x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_7; 
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = l___private_127590107__take__aux___main___rarg(x_0, x_5, x_1);
return x_7;
}
else
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_0);
x_9 = l_string_join___closed__1;
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
lean::inc(x_9);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_10);
return x_13;
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
