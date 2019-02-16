// Lean compiler output
// Module: init.lean.name_mangling
// Imports: init.lean.name init.lean.parser.string_literal
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
obj* l___private_init_lean_name__mangling_3__parse__mangled__string(obj*);
obj* l_lean_string_demangle___closed__1;
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
uint32 l_nat_digit__char(obj*);
obj* l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_name_demangle(obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux(obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
extern obj* l_mjoin___rarg___closed__1;
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(obj*);
extern obj* l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
uint8 l_char_is__digit(uint32);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__5(obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__take__aux___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(obj*);
namespace lean {
obj* string_length(obj*);
}
uint8 l_string_is__empty(obj*);
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
uint8 l_char_is__alpha(uint32);
namespace lean {
uint32 string_iterator_curr(obj*);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_function_comp___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(uint32, obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_lean_name_mangle(obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
obj* l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(obj*);
obj* l_lean_string_mangle(obj*);
obj* l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(obj*, obj*);
obj* l_string_to__nat(obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(obj*, obj*, obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
extern obj* l_char_has__repr___closed__1;
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__9(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_4__name_mangle__aux(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_id___rarg(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(uint32, obj*);
obj* l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__7(obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3(obj*);
obj* l___private_init_lean_name__mangling_6__parse__mangled__name(obj*, obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2;
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(uint32, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4___boxed(obj*, obj*);
extern obj* l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_lean_name__mangling_1__string_mangle__aux(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux(obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
extern obj* l_match__failed___rarg___closed__1;
obj* l_lean_string_demangle(obj*);
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6___boxed(obj*, obj*);
obj* l_char_quote__core(uint32);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_u");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_x");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("__");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; obj* x_7; uint32 x_10; obj* x_11; obj* x_13; uint8 x_15; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::string_iterator_curr(x_1);
x_15 = l_char_is__alpha(x_10);
if (x_15 == 0)
{
uint8 x_16; 
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
obj* x_18; obj* x_19; 
x_18 = lean::string_iterator_next(x_1);
x_19 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
else
{
if (x_15 == 0)
{
obj* x_21; 
x_21 = lean::box(0);
x_13 = x_21;
goto lbl_14;
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::string_iterator_next(x_1);
x_23 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_22;
x_2 = x_23;
goto _start;
}
}
lbl_12:
{
obj* x_26; obj* x_27; uint8 x_28; 
lean::dec(x_11);
x_26 = lean::uint32_to_nat(x_10);
x_27 = lean::mk_nat_obj(255u);
x_28 = lean::nat_dec_lt(x_26, x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint32 x_34; obj* x_35; obj* x_36; obj* x_39; obj* x_40; uint32 x_41; obj* x_42; obj* x_43; obj* x_46; obj* x_47; uint32 x_48; obj* x_49; obj* x_50; uint32 x_53; obj* x_54; obj* x_55; 
x_30 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_31 = lean::string_append(x_2, x_30);
x_32 = lean::mk_nat_obj(4096u);
x_33 = lean::nat_div(x_26, x_32);
x_34 = l_nat_digit__char(x_33);
x_35 = lean::string_push(x_31, x_34);
x_36 = lean::nat_mod(x_26, x_32);
lean::dec(x_32);
lean::dec(x_26);
x_39 = lean::mk_nat_obj(256u);
x_40 = lean::nat_div(x_36, x_39);
x_41 = l_nat_digit__char(x_40);
x_42 = lean::string_push(x_35, x_41);
x_43 = lean::nat_mod(x_36, x_39);
lean::dec(x_39);
lean::dec(x_36);
x_46 = lean::mk_nat_obj(16u);
x_47 = lean::nat_div(x_43, x_46);
x_48 = l_nat_digit__char(x_47);
x_49 = lean::string_push(x_42, x_48);
x_50 = lean::nat_mod(x_43, x_46);
lean::dec(x_46);
lean::dec(x_43);
x_53 = l_nat_digit__char(x_50);
x_54 = lean::string_push(x_49, x_53);
x_55 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_55;
x_2 = x_54;
goto _start;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; uint32 x_61; obj* x_62; obj* x_63; uint32 x_66; obj* x_67; obj* x_68; 
x_57 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_58 = lean::string_append(x_2, x_57);
x_59 = lean::mk_nat_obj(16u);
x_60 = lean::nat_div(x_26, x_59);
x_61 = l_nat_digit__char(x_60);
x_62 = lean::string_push(x_58, x_61);
x_63 = lean::nat_mod(x_26, x_59);
lean::dec(x_59);
lean::dec(x_26);
x_66 = l_nat_digit__char(x_63);
x_67 = lean::string_push(x_62, x_66);
x_68 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_68;
x_2 = x_67;
goto _start;
}
}
lbl_14:
{
uint32 x_71; uint32 x_72; uint8 x_73; uint32 x_74; 
lean::dec(x_13);
x_71 = 95;
x_72 = 55296;
x_73 = x_71 < x_72;
if (x_73 == 0)
{
uint32 x_76; uint8 x_77; 
x_76 = 57343;
x_77 = x_76 < x_71;
if (x_77 == 0)
{
uint32 x_78; 
x_78 = 0;
x_74 = x_78;
goto lbl_75;
}
else
{
uint32 x_79; uint8 x_80; 
x_79 = 1114112;
x_80 = x_71 < x_79;
if (x_80 == 0)
{
uint32 x_81; 
x_81 = 0;
x_74 = x_81;
goto lbl_75;
}
else
{
x_74 = x_71;
goto lbl_75;
}
}
}
else
{
x_74 = x_71;
goto lbl_75;
}
lbl_75:
{
uint8 x_82; 
x_82 = x_10 == x_74;
if (x_82 == 0)
{
obj* x_83; 
x_83 = lean::box(0);
x_11 = x_83;
goto lbl_12;
}
else
{
obj* x_84; obj* x_85; obj* x_86; 
x_84 = lean::string_iterator_next(x_1);
x_85 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_86 = lean::string_append(x_2, x_85);
x_0 = x_7;
x_1 = x_84;
x_2 = x_86;
goto _start;
}
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_name__mangling_1__string_mangle__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_1__string_mangle__aux___main(x_0, x_1, x_2);
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
x_5 = l___private_init_lean_name__mangling_1__string_mangle__aux___main(x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; 
lean::inc(x_0);
x_4 = l_string_is__empty(x_0);
if (x_4 == 0)
{
obj* x_5; obj* x_7; obj* x_9; 
x_5 = lean::string_length(x_0);
lean::inc(x_0);
x_7 = lean::string_mk_iterator(x_0);
lean::inc(x_2);
x_9 = l___private_init_lean_parser_parsec_1__str__aux___main(x_5, x_7, x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
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
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
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
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = lean::string_iterator_curr(x_0);
x_13 = l_char_is__digit(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_21);
x_24 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_19, x_21, x_20, x_20, x_0);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = lean::box_uint32(x_12);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_29);
return x_31;
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_16; uint32 x_17; uint32 x_18; uint8 x_19; 
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
x_14 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_16 = lean::uint32_to_nat(x_14);
x_17 = 48;
x_18 = 55296;
x_19 = x_17 < x_18;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 57343;
x_21 = x_20 < x_17;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_22 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_23 = lean::nat_sub(x_16, x_22);
lean::dec(x_16);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_9);
lean::cnstr_set(x_27, 2, x_25);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_30; obj* x_32; 
lean::dec(x_0);
x_30 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_30);
return x_32;
}
else
{
obj* x_33; uint8 x_35; 
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
x_1 = x_28;
x_2 = x_33;
x_3 = x_35;
goto lbl_4;
}
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 1114112;
x_37 = x_17 < x_36;
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; 
x_38 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_39 = lean::nat_sub(x_16, x_38);
lean::dec(x_16);
x_41 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_41);
if (lean::is_scalar(x_13)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_13;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_9);
lean::cnstr_set(x_43, 2, x_41);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; 
lean::dec(x_0);
x_46 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_44, x_46);
return x_48;
}
else
{
obj* x_49; uint8 x_51; 
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
x_1 = x_44;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
else
{
obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
x_52 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_53 = lean::nat_sub(x_16, x_52);
lean::dec(x_16);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
if (lean::is_scalar(x_13)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_13;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_9);
lean::cnstr_set(x_57, 2, x_55);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; 
lean::dec(x_0);
x_60 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_60);
return x_62;
}
else
{
obj* x_63; uint8 x_65; 
x_63 = lean::cnstr_get(x_58, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_58, sizeof(void*)*1);
x_1 = x_58;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
else
{
obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; 
x_66 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_67 = lean::nat_sub(x_16, x_66);
lean::dec(x_16);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_69);
if (lean::is_scalar(x_13)) {
 x_71 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_71 = x_13;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set(x_71, 1, x_9);
lean::cnstr_set(x_71, 2, x_69);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; 
lean::dec(x_0);
x_74 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_74);
x_76 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_72, x_74);
return x_76;
}
else
{
obj* x_77; uint8 x_79; 
x_77 = lean::cnstr_get(x_72, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
x_1 = x_72;
x_2 = x_77;
x_3 = x_79;
goto lbl_4;
}
}
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_85; obj* x_86; 
x_80 = lean::cnstr_get(x_6, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_83 = x_6;
}
lean::inc(x_80);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_80);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_82);
x_86 = x_85;
x_1 = x_86;
x_2 = x_80;
x_3 = x_82;
goto lbl_4;
}
lbl_4:
{
obj* x_87; obj* x_88; uint8 x_89; 
if (x_3 == 0)
{
obj* x_92; uint8 x_94; 
lean::dec(x_1);
x_94 = lean::string_iterator_has_next(x_0);
if (x_94 == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_102; 
x_95 = lean::box(0);
x_96 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_97 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_95);
lean::inc(x_97);
lean::inc(x_96);
x_102 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_96, x_97, x_95, x_95, x_0);
x_92 = x_102;
goto lbl_93;
}
else
{
uint32 x_103; obj* x_104; obj* x_106; uint32 x_108; uint32 x_109; uint8 x_110; uint8 x_111; 
x_103 = lean::string_iterator_curr(x_0);
x_108 = 97;
x_109 = 55296;
x_110 = x_108 < x_109;
if (x_110 == 0)
{
uint32 x_113; uint8 x_114; 
x_113 = 57343;
x_114 = x_113 < x_108;
if (x_114 == 0)
{
uint32 x_115; uint8 x_116; 
x_115 = 0;
x_116 = x_115 <= x_103;
if (x_116 == 0)
{
obj* x_117; 
x_117 = lean::box(0);
x_104 = x_117;
goto lbl_105;
}
else
{
uint8 x_118; 
x_118 = 1;
x_111 = x_118;
goto lbl_112;
}
}
else
{
uint32 x_119; uint8 x_120; 
x_119 = 1114112;
x_120 = x_108 < x_119;
if (x_120 == 0)
{
uint32 x_121; uint8 x_122; 
x_121 = 0;
x_122 = x_121 <= x_103;
if (x_122 == 0)
{
obj* x_123; 
x_123 = lean::box(0);
x_104 = x_123;
goto lbl_105;
}
else
{
uint8 x_124; 
x_124 = 1;
x_111 = x_124;
goto lbl_112;
}
}
else
{
uint8 x_125; 
x_125 = x_108 <= x_103;
if (x_125 == 0)
{
obj* x_126; 
x_126 = lean::box(0);
x_104 = x_126;
goto lbl_105;
}
else
{
uint8 x_127; 
x_127 = 1;
x_111 = x_127;
goto lbl_112;
}
}
}
}
else
{
uint8 x_128; 
x_128 = x_108 <= x_103;
if (x_128 == 0)
{
obj* x_129; 
x_129 = lean::box(0);
x_104 = x_129;
goto lbl_105;
}
else
{
uint8 x_130; 
x_130 = 1;
x_111 = x_130;
goto lbl_112;
}
}
lbl_105:
{
obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_143; 
lean::dec(x_104);
x_132 = l_char_quote__core(x_103);
x_133 = l_char_has__repr___closed__1;
lean::inc(x_133);
x_135 = lean::string_append(x_133, x_132);
lean::dec(x_132);
x_137 = lean::string_append(x_135, x_133);
x_138 = lean::box(0);
x_139 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_138);
lean::inc(x_139);
x_143 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_137, x_139, x_138, x_138, x_0);
x_92 = x_143;
goto lbl_93;
}
lbl_107:
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_106);
lean::inc(x_0);
x_146 = lean::string_iterator_next(x_0);
x_147 = lean::box(0);
x_148 = lean::box_uint32(x_103);
x_149 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_146);
lean::cnstr_set(x_149, 2, x_147);
x_92 = x_149;
goto lbl_93;
}
lbl_112:
{
uint32 x_150; uint8 x_151; 
x_150 = 102;
x_151 = x_150 < x_109;
if (x_151 == 0)
{
uint32 x_152; uint8 x_153; 
x_152 = 57343;
x_153 = x_152 < x_150;
if (x_153 == 0)
{
uint32 x_154; uint8 x_155; 
x_154 = 0;
x_155 = x_103 <= x_154;
if (x_155 == 0)
{
obj* x_156; 
x_156 = lean::box(0);
x_104 = x_156;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_157; 
x_157 = lean::box(0);
x_104 = x_157;
goto lbl_105;
}
else
{
obj* x_158; 
x_158 = lean::box(0);
x_106 = x_158;
goto lbl_107;
}
}
}
else
{
uint32 x_159; uint8 x_160; 
x_159 = 1114112;
x_160 = x_150 < x_159;
if (x_160 == 0)
{
uint32 x_161; uint8 x_162; 
x_161 = 0;
x_162 = x_103 <= x_161;
if (x_162 == 0)
{
obj* x_163; 
x_163 = lean::box(0);
x_104 = x_163;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_164; 
x_164 = lean::box(0);
x_104 = x_164;
goto lbl_105;
}
else
{
obj* x_165; 
x_165 = lean::box(0);
x_106 = x_165;
goto lbl_107;
}
}
}
else
{
uint8 x_166; 
x_166 = x_103 <= x_150;
if (x_166 == 0)
{
obj* x_167; 
x_167 = lean::box(0);
x_104 = x_167;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_168; 
x_168 = lean::box(0);
x_104 = x_168;
goto lbl_105;
}
else
{
obj* x_169; 
x_169 = lean::box(0);
x_106 = x_169;
goto lbl_107;
}
}
}
}
}
else
{
uint8 x_170; 
x_170 = x_103 <= x_150;
if (x_170 == 0)
{
obj* x_171; 
x_171 = lean::box(0);
x_104 = x_171;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_172; 
x_172 = lean::box(0);
x_104 = x_172;
goto lbl_105;
}
else
{
obj* x_173; 
x_173 = lean::box(0);
x_106 = x_173;
goto lbl_107;
}
}
}
}
}
lbl_93:
{
obj* x_174; obj* x_176; 
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_92);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_183; uint32 x_184; obj* x_186; uint32 x_187; uint32 x_188; uint8 x_189; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 2);
lean::inc(x_181);
if (lean::is_shared(x_176)) {
 lean::dec(x_176);
 x_183 = lean::box(0);
} else {
 lean::cnstr_release(x_176, 0);
 lean::cnstr_release(x_176, 1);
 lean::cnstr_release(x_176, 2);
 x_183 = x_176;
}
x_184 = lean::unbox_uint32(x_177);
lean::dec(x_177);
x_186 = lean::uint32_to_nat(x_184);
x_187 = 97;
x_188 = 55296;
x_189 = x_187 < x_188;
if (x_189 == 0)
{
uint32 x_190; uint8 x_191; 
x_190 = 57343;
x_191 = x_190 < x_187;
if (x_191 == 0)
{
obj* x_192; obj* x_193; obj* x_195; obj* x_196; obj* x_200; obj* x_201; 
x_192 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_193 = lean::nat_sub(x_186, x_192);
lean::dec(x_186);
x_195 = lean::mk_nat_obj(10u);
x_196 = lean::nat_add(x_195, x_193);
lean::dec(x_193);
lean::dec(x_195);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_200 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_200 = x_183;
}
lean::cnstr_set(x_200, 0, x_196);
lean::cnstr_set(x_200, 1, x_179);
lean::cnstr_set(x_200, 2, x_174);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_200);
if (lean::obj_tag(x_201) == 0)
{
obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_0);
x_203 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_201);
x_204 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_204);
x_206 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_203, x_204);
return x_206;
}
else
{
obj* x_207; uint8 x_209; 
x_207 = lean::cnstr_get(x_201, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get_scalar<uint8>(x_201, sizeof(void*)*1);
x_87 = x_201;
x_88 = x_207;
x_89 = x_209;
goto lbl_90;
}
}
else
{
uint32 x_210; uint8 x_211; 
x_210 = 1114112;
x_211 = x_187 < x_210;
if (x_211 == 0)
{
obj* x_212; obj* x_213; obj* x_215; obj* x_216; obj* x_220; obj* x_221; 
x_212 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_213 = lean::nat_sub(x_186, x_212);
lean::dec(x_186);
x_215 = lean::mk_nat_obj(10u);
x_216 = lean::nat_add(x_215, x_213);
lean::dec(x_213);
lean::dec(x_215);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_220 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_220 = x_183;
}
lean::cnstr_set(x_220, 0, x_216);
lean::cnstr_set(x_220, 1, x_179);
lean::cnstr_set(x_220, 2, x_174);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_0);
x_223 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_221);
x_224 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_224);
x_226 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_223, x_224);
return x_226;
}
else
{
obj* x_227; uint8 x_229; 
x_227 = lean::cnstr_get(x_221, 0);
lean::inc(x_227);
x_229 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
x_87 = x_221;
x_88 = x_227;
x_89 = x_229;
goto lbl_90;
}
}
else
{
obj* x_230; obj* x_231; obj* x_233; obj* x_234; obj* x_238; obj* x_239; 
x_230 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_231 = lean::nat_sub(x_186, x_230);
lean::dec(x_186);
x_233 = lean::mk_nat_obj(10u);
x_234 = lean::nat_add(x_233, x_231);
lean::dec(x_231);
lean::dec(x_233);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_238 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_238 = x_183;
}
lean::cnstr_set(x_238, 0, x_234);
lean::cnstr_set(x_238, 1, x_179);
lean::cnstr_set(x_238, 2, x_174);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_0);
x_241 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_239);
x_242 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_242);
x_244 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_241, x_242);
return x_244;
}
else
{
obj* x_245; uint8 x_247; 
x_245 = lean::cnstr_get(x_239, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get_scalar<uint8>(x_239, sizeof(void*)*1);
x_87 = x_239;
x_88 = x_245;
x_89 = x_247;
goto lbl_90;
}
}
}
}
else
{
obj* x_248; obj* x_249; obj* x_251; obj* x_252; obj* x_256; obj* x_257; 
x_248 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_249 = lean::nat_sub(x_186, x_248);
lean::dec(x_186);
x_251 = lean::mk_nat_obj(10u);
x_252 = lean::nat_add(x_251, x_249);
lean::dec(x_249);
lean::dec(x_251);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_256 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_256 = x_183;
}
lean::cnstr_set(x_256, 0, x_252);
lean::cnstr_set(x_256, 1, x_179);
lean::cnstr_set(x_256, 2, x_174);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_256);
if (lean::obj_tag(x_257) == 0)
{
obj* x_259; obj* x_260; obj* x_262; 
lean::dec(x_0);
x_259 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_257);
x_260 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_260);
x_262 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_259, x_260);
return x_262;
}
else
{
obj* x_263; uint8 x_265; 
x_263 = lean::cnstr_get(x_257, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get_scalar<uint8>(x_257, sizeof(void*)*1);
x_87 = x_257;
x_88 = x_263;
x_89 = x_265;
goto lbl_90;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_271; obj* x_272; 
x_266 = lean::cnstr_get(x_176, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_shared(x_176)) {
 lean::dec(x_176);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_176, 0);
 x_269 = x_176;
}
lean::inc(x_266);
if (lean::is_scalar(x_269)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_269;
}
lean::cnstr_set(x_271, 0, x_266);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_268);
x_272 = x_271;
x_87 = x_272;
x_88 = x_266;
x_89 = x_268;
goto lbl_90;
}
}
}
else
{
obj* x_275; obj* x_277; 
lean::dec(x_0);
lean::dec(x_2);
x_275 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_275);
x_277 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_275);
return x_277;
}
lbl_90:
{
if (x_89 == 0)
{
obj* x_279; uint8 x_281; 
lean::dec(x_87);
x_281 = lean::string_iterator_has_next(x_0);
if (x_281 == 0)
{
obj* x_282; obj* x_283; obj* x_284; obj* x_288; 
x_282 = lean::box(0);
x_283 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_284 = l_mjoin___rarg___closed__1;
lean::inc(x_282);
lean::inc(x_284);
lean::inc(x_283);
x_288 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_283, x_284, x_282, x_282, x_0);
x_279 = x_288;
goto lbl_280;
}
else
{
uint32 x_289; obj* x_290; obj* x_292; uint32 x_294; uint32 x_295; uint8 x_296; uint8 x_297; 
x_289 = lean::string_iterator_curr(x_0);
x_294 = 65;
x_295 = 55296;
x_296 = x_294 < x_295;
if (x_296 == 0)
{
uint32 x_299; uint8 x_300; 
x_299 = 57343;
x_300 = x_299 < x_294;
if (x_300 == 0)
{
uint32 x_301; uint8 x_302; 
x_301 = 0;
x_302 = x_301 <= x_289;
if (x_302 == 0)
{
obj* x_303; 
x_303 = lean::box(0);
x_290 = x_303;
goto lbl_291;
}
else
{
uint8 x_304; 
x_304 = 1;
x_297 = x_304;
goto lbl_298;
}
}
else
{
uint32 x_305; uint8 x_306; 
x_305 = 1114112;
x_306 = x_294 < x_305;
if (x_306 == 0)
{
uint32 x_307; uint8 x_308; 
x_307 = 0;
x_308 = x_307 <= x_289;
if (x_308 == 0)
{
obj* x_309; 
x_309 = lean::box(0);
x_290 = x_309;
goto lbl_291;
}
else
{
uint8 x_310; 
x_310 = 1;
x_297 = x_310;
goto lbl_298;
}
}
else
{
uint8 x_311; 
x_311 = x_294 <= x_289;
if (x_311 == 0)
{
obj* x_312; 
x_312 = lean::box(0);
x_290 = x_312;
goto lbl_291;
}
else
{
uint8 x_313; 
x_313 = 1;
x_297 = x_313;
goto lbl_298;
}
}
}
}
else
{
uint8 x_314; 
x_314 = x_294 <= x_289;
if (x_314 == 0)
{
obj* x_315; 
x_315 = lean::box(0);
x_290 = x_315;
goto lbl_291;
}
else
{
uint8 x_316; 
x_316 = 1;
x_297 = x_316;
goto lbl_298;
}
}
lbl_291:
{
obj* x_318; obj* x_319; obj* x_321; obj* x_323; obj* x_324; obj* x_325; obj* x_328; 
lean::dec(x_290);
x_318 = l_char_quote__core(x_289);
x_319 = l_char_has__repr___closed__1;
lean::inc(x_319);
x_321 = lean::string_append(x_319, x_318);
lean::dec(x_318);
x_323 = lean::string_append(x_321, x_319);
x_324 = lean::box(0);
x_325 = l_mjoin___rarg___closed__1;
lean::inc(x_324);
lean::inc(x_325);
x_328 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_323, x_325, x_324, x_324, x_0);
x_279 = x_328;
goto lbl_280;
}
lbl_293:
{
obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
lean::dec(x_292);
x_330 = lean::string_iterator_next(x_0);
x_331 = lean::box(0);
x_332 = lean::box_uint32(x_289);
x_333 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_330);
lean::cnstr_set(x_333, 2, x_331);
x_279 = x_333;
goto lbl_280;
}
lbl_298:
{
uint32 x_334; uint8 x_335; 
x_334 = 70;
x_335 = x_334 < x_295;
if (x_335 == 0)
{
uint32 x_336; uint8 x_337; 
x_336 = 57343;
x_337 = x_336 < x_334;
if (x_337 == 0)
{
uint32 x_338; uint8 x_339; 
x_338 = 0;
x_339 = x_289 <= x_338;
if (x_339 == 0)
{
obj* x_340; 
x_340 = lean::box(0);
x_290 = x_340;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_341; 
x_341 = lean::box(0);
x_290 = x_341;
goto lbl_291;
}
else
{
obj* x_342; 
x_342 = lean::box(0);
x_292 = x_342;
goto lbl_293;
}
}
}
else
{
uint32 x_343; uint8 x_344; 
x_343 = 1114112;
x_344 = x_334 < x_343;
if (x_344 == 0)
{
uint32 x_345; uint8 x_346; 
x_345 = 0;
x_346 = x_289 <= x_345;
if (x_346 == 0)
{
obj* x_347; 
x_347 = lean::box(0);
x_290 = x_347;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_348; 
x_348 = lean::box(0);
x_290 = x_348;
goto lbl_291;
}
else
{
obj* x_349; 
x_349 = lean::box(0);
x_292 = x_349;
goto lbl_293;
}
}
}
else
{
uint8 x_350; 
x_350 = x_289 <= x_334;
if (x_350 == 0)
{
obj* x_351; 
x_351 = lean::box(0);
x_290 = x_351;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_352; 
x_352 = lean::box(0);
x_290 = x_352;
goto lbl_291;
}
else
{
obj* x_353; 
x_353 = lean::box(0);
x_292 = x_353;
goto lbl_293;
}
}
}
}
}
else
{
uint8 x_354; 
x_354 = x_289 <= x_334;
if (x_354 == 0)
{
obj* x_355; 
x_355 = lean::box(0);
x_290 = x_355;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_356; 
x_356 = lean::box(0);
x_290 = x_356;
goto lbl_291;
}
else
{
obj* x_357; 
x_357 = lean::box(0);
x_292 = x_357;
goto lbl_293;
}
}
}
}
}
lbl_280:
{
obj* x_358; obj* x_360; 
x_358 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_358);
x_360 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_279);
if (lean::obj_tag(x_360) == 0)
{
obj* x_361; obj* x_363; obj* x_365; obj* x_367; uint32 x_368; obj* x_370; uint32 x_371; uint32 x_372; uint8 x_373; 
x_361 = lean::cnstr_get(x_360, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_360, 2);
lean::inc(x_365);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 lean::cnstr_release(x_360, 1);
 lean::cnstr_release(x_360, 2);
 x_367 = x_360;
}
x_368 = lean::unbox_uint32(x_361);
lean::dec(x_361);
x_370 = lean::uint32_to_nat(x_368);
x_371 = 65;
x_372 = 55296;
x_373 = x_371 < x_372;
if (x_373 == 0)
{
uint32 x_374; uint8 x_375; 
x_374 = 57343;
x_375 = x_374 < x_371;
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_379; obj* x_380; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_390; 
x_376 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_377 = lean::nat_sub(x_370, x_376);
lean::dec(x_370);
x_379 = lean::mk_nat_obj(10u);
x_380 = lean::nat_add(x_379, x_377);
lean::dec(x_377);
lean::dec(x_379);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_384 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_384 = x_367;
}
lean::cnstr_set(x_384, 0, x_380);
lean::cnstr_set(x_384, 1, x_363);
lean::cnstr_set(x_384, 2, x_358);
x_385 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_384);
x_386 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_385);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_386);
x_388 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_388);
x_390 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_387, x_388);
return x_390;
}
else
{
uint32 x_391; uint8 x_392; 
x_391 = 1114112;
x_392 = x_371 < x_391;
if (x_392 == 0)
{
obj* x_393; obj* x_394; obj* x_396; obj* x_397; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_407; 
x_393 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_394 = lean::nat_sub(x_370, x_393);
lean::dec(x_370);
x_396 = lean::mk_nat_obj(10u);
x_397 = lean::nat_add(x_396, x_394);
lean::dec(x_394);
lean::dec(x_396);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_401 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_401 = x_367;
}
lean::cnstr_set(x_401, 0, x_397);
lean::cnstr_set(x_401, 1, x_363);
lean::cnstr_set(x_401, 2, x_358);
x_402 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_401);
x_403 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_402);
x_404 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_403);
x_405 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_405);
x_407 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_404, x_405);
return x_407;
}
else
{
obj* x_408; obj* x_409; obj* x_411; obj* x_412; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_422; 
x_408 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_409 = lean::nat_sub(x_370, x_408);
lean::dec(x_370);
x_411 = lean::mk_nat_obj(10u);
x_412 = lean::nat_add(x_411, x_409);
lean::dec(x_409);
lean::dec(x_411);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_416 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_416 = x_367;
}
lean::cnstr_set(x_416, 0, x_412);
lean::cnstr_set(x_416, 1, x_363);
lean::cnstr_set(x_416, 2, x_358);
x_417 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_416);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_417);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_418);
x_420 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_420);
x_422 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_419, x_420);
return x_422;
}
}
}
else
{
obj* x_423; obj* x_424; obj* x_426; obj* x_427; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_437; 
x_423 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_424 = lean::nat_sub(x_370, x_423);
lean::dec(x_370);
x_426 = lean::mk_nat_obj(10u);
x_427 = lean::nat_add(x_426, x_424);
lean::dec(x_424);
lean::dec(x_426);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_431 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_431 = x_367;
}
lean::cnstr_set(x_431, 0, x_427);
lean::cnstr_set(x_431, 1, x_363);
lean::cnstr_set(x_431, 2, x_358);
x_432 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_431);
x_433 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_432);
x_434 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_433);
x_435 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_435);
x_437 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_434, x_435);
return x_437;
}
}
else
{
obj* x_438; uint8 x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_448; 
x_438 = lean::cnstr_get(x_360, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get_scalar<uint8>(x_360, sizeof(void*)*1);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_441 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 x_441 = x_360;
}
if (lean::is_scalar(x_441)) {
 x_442 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_442 = x_441;
}
lean::cnstr_set(x_442, 0, x_438);
lean::cnstr_set_scalar(x_442, sizeof(void*)*1, x_440);
x_443 = x_442;
x_444 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_443);
x_445 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_444);
x_446 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_446);
x_448 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_445, x_446);
return x_448;
}
}
}
else
{
obj* x_451; obj* x_452; obj* x_454; 
lean::dec(x_88);
lean::dec(x_0);
x_451 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_87);
x_452 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_452);
x_454 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_451, x_452);
return x_454;
}
}
}
}
}
obj* l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = lean::string_iterator_curr(x_0);
x_13 = l_char_is__alpha(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_21);
x_24 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_19, x_21, x_20, x_20, x_0);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = lean::box_uint32(x_12);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_29);
return x_31;
}
}
}
}
obj* _init_l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1() {
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
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint32 x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_20; 
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
x_17 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_12, x_14, x_13, x_13, x_0);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_17);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_24; 
x_21 = lean::box(0);
x_22 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_0);
lean::cnstr_set(x_24, 2, x_22);
return x_24;
}
}
}
obj* _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1() {
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
obj* _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2() {
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
obj* _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3() {
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
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_13; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
lean::inc(x_2);
x_13 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
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
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
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
lean::dec(x_2);
return x_10;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_33 = lean::cnstr_get(x_10, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_35 == 0)
{
obj* x_42; 
lean::dec(x_10);
lean::inc(x_2);
x_42 = l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; uint32 x_50; obj* x_53; obj* x_55; obj* x_56; 
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
lean::inc(x_7);
x_55 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_53, x_45);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_60 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_56);
return x_60;
}
else
{
obj* x_61; uint8 x_63; 
x_61 = lean::cnstr_get(x_56, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
x_36 = x_56;
x_37 = x_61;
x_38 = x_63;
goto lbl_39;
}
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_69; obj* x_70; 
x_64 = lean::cnstr_get(x_42, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_67 = x_42;
}
lean::inc(x_64);
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_66);
x_70 = x_69;
x_36 = x_70;
x_37 = x_64;
x_38 = x_66;
goto lbl_39;
}
}
else
{
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_33);
return x_10;
}
lbl_39:
{
obj* x_75; obj* x_76; uint8 x_77; 
if (x_38 == 0)
{
obj* x_81; 
lean::dec(x_36);
lean::inc(x_2);
x_81 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_84; obj* x_86; uint32 x_89; obj* x_92; obj* x_94; obj* x_95; 
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 2);
lean::inc(x_86);
lean::dec(x_81);
x_89 = lean::unbox_uint32(x_82);
lean::dec(x_82);
lean::inc(x_1);
x_92 = lean::string_push(x_1, x_89);
lean::inc(x_7);
x_94 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_92, x_84);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_99; obj* x_100; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_99 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_95);
x_100 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_99);
return x_100;
}
else
{
obj* x_101; uint8 x_103; 
x_101 = lean::cnstr_get(x_95, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
x_75 = x_95;
x_76 = x_101;
x_77 = x_103;
goto lbl_78;
}
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_109; obj* x_110; 
x_104 = lean::cnstr_get(x_81, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_81, sizeof(void*)*1);
if (lean::is_shared(x_81)) {
 lean::dec(x_81);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_81, 0);
 x_107 = x_81;
}
lean::inc(x_104);
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_106);
x_110 = x_109;
x_75 = x_110;
x_76 = x_104;
x_77 = x_106;
goto lbl_78;
}
}
else
{
obj* x_115; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_37);
x_115 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_36);
return x_115;
}
lbl_78:
{
obj* x_116; obj* x_117; uint8 x_118; 
if (x_77 == 0)
{
obj* x_121; obj* x_122; obj* x_126; 
lean::dec(x_75);
x_121 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_122 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
lean::inc(x_122);
lean::inc(x_121);
x_126 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_121, x_122, x_2);
if (lean::obj_tag(x_126) == 0)
{
obj* x_127; obj* x_129; uint32 x_132; uint32 x_133; uint8 x_134; 
x_127 = lean::cnstr_get(x_126, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 2);
lean::inc(x_129);
lean::dec(x_126);
x_132 = 95;
x_133 = 55296;
x_134 = x_132 < x_133;
if (x_134 == 0)
{
uint32 x_135; uint8 x_136; 
x_135 = 57343;
x_136 = x_135 < x_132;
if (x_136 == 0)
{
uint32 x_137; obj* x_139; obj* x_141; obj* x_142; 
x_137 = 0;
lean::inc(x_1);
x_139 = lean::string_push(x_1, x_137);
lean::inc(x_7);
x_141 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_139, x_127);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_146; obj* x_147; obj* x_148; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_146 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_142);
x_147 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_146);
x_148 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_147);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_142, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_142, sizeof(void*)*1);
x_116 = x_142;
x_117 = x_149;
x_118 = x_151;
goto lbl_119;
}
}
else
{
uint32 x_152; uint8 x_153; 
x_152 = 1114112;
x_153 = x_132 < x_152;
if (x_153 == 0)
{
uint32 x_154; obj* x_156; obj* x_158; obj* x_159; 
x_154 = 0;
lean::inc(x_1);
x_156 = lean::string_push(x_1, x_154);
lean::inc(x_7);
x_158 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_156, x_127);
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_158);
if (lean::obj_tag(x_159) == 0)
{
obj* x_163; obj* x_164; obj* x_165; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_163 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_159);
x_164 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_163);
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_164);
return x_165;
}
else
{
obj* x_166; uint8 x_168; 
x_166 = lean::cnstr_get(x_159, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<uint8>(x_159, sizeof(void*)*1);
x_116 = x_159;
x_117 = x_166;
x_118 = x_168;
goto lbl_119;
}
}
else
{
obj* x_170; obj* x_172; obj* x_173; 
lean::inc(x_1);
x_170 = lean::string_push(x_1, x_132);
lean::inc(x_7);
x_172 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_170, x_127);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_177 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_173);
x_178 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_177);
x_179 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_178);
return x_179;
}
else
{
obj* x_180; uint8 x_182; 
x_180 = lean::cnstr_get(x_173, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
x_116 = x_173;
x_117 = x_180;
x_118 = x_182;
goto lbl_119;
}
}
}
}
else
{
obj* x_184; obj* x_186; obj* x_187; 
lean::inc(x_1);
x_184 = lean::string_push(x_1, x_132);
lean::inc(x_7);
x_186 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_184, x_127);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_186);
if (lean::obj_tag(x_187) == 0)
{
obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_191 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_187);
x_192 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_191);
x_193 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_192);
return x_193;
}
else
{
obj* x_194; uint8 x_196; 
x_194 = lean::cnstr_get(x_187, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*1);
x_116 = x_187;
x_117 = x_194;
x_118 = x_196;
goto lbl_119;
}
}
}
else
{
obj* x_197; uint8 x_199; obj* x_200; obj* x_202; obj* x_203; 
x_197 = lean::cnstr_get(x_126, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_200 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_200 = x_126;
}
lean::inc(x_197);
if (lean::is_scalar(x_200)) {
 x_202 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_202 = x_200;
}
lean::cnstr_set(x_202, 0, x_197);
lean::cnstr_set_scalar(x_202, sizeof(void*)*1, x_199);
x_203 = x_202;
x_116 = x_203;
x_117 = x_197;
x_118 = x_199;
goto lbl_119;
}
}
else
{
obj* x_208; obj* x_209; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_76);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_75);
x_209 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_208);
return x_209;
}
lbl_119:
{
obj* x_210; obj* x_211; uint8 x_212; 
if (x_118 == 0)
{
obj* x_215; obj* x_216; obj* x_220; 
lean::dec(x_116);
x_215 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_216 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_216);
lean::inc(x_215);
x_220 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_215, x_216, x_2);
if (lean::obj_tag(x_220) == 0)
{
obj* x_221; obj* x_223; obj* x_226; 
x_221 = lean::cnstr_get(x_220, 1);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_220, 2);
lean::inc(x_223);
lean::dec(x_220);
x_226 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_221);
if (lean::obj_tag(x_226) == 0)
{
obj* x_227; obj* x_229; obj* x_231; obj* x_234; 
x_227 = lean::cnstr_get(x_226, 0);
lean::inc(x_227);
x_229 = lean::cnstr_get(x_226, 1);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_226, 2);
lean::inc(x_231);
lean::dec(x_226);
x_234 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_229);
if (lean::obj_tag(x_234) == 0)
{
obj* x_235; obj* x_237; obj* x_239; obj* x_242; obj* x_243; obj* x_246; uint32 x_249; uint32 x_251; uint8 x_252; 
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_234, 2);
lean::inc(x_239);
lean::dec(x_234);
x_242 = lean::mk_nat_obj(16u);
x_243 = lean::nat_mul(x_227, x_242);
lean::dec(x_242);
lean::dec(x_227);
x_246 = lean::nat_add(x_243, x_235);
lean::dec(x_235);
lean::dec(x_243);
x_249 = lean::uint32_of_nat(x_246);
lean::dec(x_246);
x_251 = 55296;
x_252 = x_249 < x_251;
if (x_252 == 0)
{
uint32 x_253; uint8 x_254; 
x_253 = 57343;
x_254 = x_253 < x_249;
if (x_254 == 0)
{
uint32 x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_261; obj* x_262; 
x_255 = 0;
lean::inc(x_1);
x_257 = lean::string_push(x_1, x_255);
lean::inc(x_7);
x_259 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_257, x_237);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_259);
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_260);
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_261);
if (lean::obj_tag(x_262) == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_266 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_262);
x_267 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_266);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_267);
x_269 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_268);
return x_269;
}
else
{
obj* x_270; uint8 x_272; 
x_270 = lean::cnstr_get(x_262, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get_scalar<uint8>(x_262, sizeof(void*)*1);
x_210 = x_262;
x_211 = x_270;
x_212 = x_272;
goto lbl_213;
}
}
else
{
uint32 x_273; uint8 x_274; 
x_273 = 1114112;
x_274 = x_249 < x_273;
if (x_274 == 0)
{
uint32 x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_275 = 0;
lean::inc(x_1);
x_277 = lean::string_push(x_1, x_275);
lean::inc(x_7);
x_279 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_277, x_237);
x_280 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_279);
x_281 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_280);
x_282 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_281);
if (lean::obj_tag(x_282) == 0)
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_282);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_286);
x_288 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_287);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_288);
return x_289;
}
else
{
obj* x_290; uint8 x_292; 
x_290 = lean::cnstr_get(x_282, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get_scalar<uint8>(x_282, sizeof(void*)*1);
x_210 = x_282;
x_211 = x_290;
x_212 = x_292;
goto lbl_213;
}
}
else
{
obj* x_294; obj* x_296; obj* x_297; obj* x_298; obj* x_299; 
lean::inc(x_1);
x_294 = lean::string_push(x_1, x_249);
lean::inc(x_7);
x_296 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_294, x_237);
x_297 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_296);
x_298 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_297);
x_299 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_298);
if (lean::obj_tag(x_299) == 0)
{
obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_303 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_299);
x_304 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_303);
x_305 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_304);
x_306 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_305);
return x_306;
}
else
{
obj* x_307; uint8 x_309; 
x_307 = lean::cnstr_get(x_299, 0);
lean::inc(x_307);
x_309 = lean::cnstr_get_scalar<uint8>(x_299, sizeof(void*)*1);
x_210 = x_299;
x_211 = x_307;
x_212 = x_309;
goto lbl_213;
}
}
}
}
else
{
obj* x_311; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
lean::inc(x_1);
x_311 = lean::string_push(x_1, x_249);
lean::inc(x_7);
x_313 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_311, x_237);
x_314 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_313);
x_315 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_314);
x_316 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_315);
if (lean::obj_tag(x_316) == 0)
{
obj* x_320; obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_320 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_316);
x_321 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_320);
x_322 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_321);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_322);
return x_323;
}
else
{
obj* x_324; uint8 x_326; 
x_324 = lean::cnstr_get(x_316, 0);
lean::inc(x_324);
x_326 = lean::cnstr_get_scalar<uint8>(x_316, sizeof(void*)*1);
x_210 = x_316;
x_211 = x_324;
x_212 = x_326;
goto lbl_213;
}
}
}
else
{
obj* x_328; uint8 x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
lean::dec(x_227);
x_328 = lean::cnstr_get(x_234, 0);
lean::inc(x_328);
x_330 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
if (lean::is_shared(x_234)) {
 lean::dec(x_234);
 x_331 = lean::box(0);
} else {
 lean::cnstr_release(x_234, 0);
 x_331 = x_234;
}
if (lean::is_scalar(x_331)) {
 x_332 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_332 = x_331;
}
lean::cnstr_set(x_332, 0, x_328);
lean::cnstr_set_scalar(x_332, sizeof(void*)*1, x_330);
x_333 = x_332;
x_334 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_333);
x_335 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_334);
if (lean::obj_tag(x_335) == 0)
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_339 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_335);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_339);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_340);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_341);
return x_342;
}
else
{
obj* x_343; uint8 x_345; 
x_343 = lean::cnstr_get(x_335, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get_scalar<uint8>(x_335, sizeof(void*)*1);
x_210 = x_335;
x_211 = x_343;
x_212 = x_345;
goto lbl_213;
}
}
}
else
{
obj* x_346; uint8 x_348; obj* x_349; obj* x_350; obj* x_351; obj* x_352; 
x_346 = lean::cnstr_get(x_226, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get_scalar<uint8>(x_226, sizeof(void*)*1);
if (lean::is_shared(x_226)) {
 lean::dec(x_226);
 x_349 = lean::box(0);
} else {
 lean::cnstr_release(x_226, 0);
 x_349 = x_226;
}
if (lean::is_scalar(x_349)) {
 x_350 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_350 = x_349;
}
lean::cnstr_set(x_350, 0, x_346);
lean::cnstr_set_scalar(x_350, sizeof(void*)*1, x_348);
x_351 = x_350;
x_352 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_223, x_351);
if (lean::obj_tag(x_352) == 0)
{
obj* x_356; obj* x_357; obj* x_358; obj* x_359; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_356 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_352);
x_357 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_356);
x_358 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_357);
x_359 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_358);
return x_359;
}
else
{
obj* x_360; uint8 x_362; 
x_360 = lean::cnstr_get(x_352, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get_scalar<uint8>(x_352, sizeof(void*)*1);
x_210 = x_352;
x_211 = x_360;
x_212 = x_362;
goto lbl_213;
}
}
}
else
{
obj* x_363; uint8 x_365; obj* x_366; obj* x_368; obj* x_369; 
x_363 = lean::cnstr_get(x_220, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get_scalar<uint8>(x_220, sizeof(void*)*1);
if (lean::is_shared(x_220)) {
 lean::dec(x_220);
 x_366 = lean::box(0);
} else {
 lean::cnstr_release(x_220, 0);
 x_366 = x_220;
}
lean::inc(x_363);
if (lean::is_scalar(x_366)) {
 x_368 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_368 = x_366;
}
lean::cnstr_set(x_368, 0, x_363);
lean::cnstr_set_scalar(x_368, sizeof(void*)*1, x_365);
x_369 = x_368;
x_210 = x_369;
x_211 = x_363;
x_212 = x_365;
goto lbl_213;
}
}
else
{
obj* x_374; obj* x_375; obj* x_376; 
lean::dec(x_117);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_374 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_116);
x_375 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_374);
x_376 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_375);
return x_376;
}
lbl_213:
{
if (x_212 == 0)
{
obj* x_378; obj* x_379; obj* x_382; 
lean::dec(x_210);
x_378 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_379 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
lean::inc(x_379);
lean::inc(x_378);
x_382 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_378, x_379, x_2);
if (lean::obj_tag(x_382) == 0)
{
obj* x_383; obj* x_385; obj* x_388; 
x_383 = lean::cnstr_get(x_382, 1);
lean::inc(x_383);
x_385 = lean::cnstr_get(x_382, 2);
lean::inc(x_385);
lean::dec(x_382);
x_388 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_383);
if (lean::obj_tag(x_388) == 0)
{
obj* x_389; obj* x_391; obj* x_393; obj* x_396; 
x_389 = lean::cnstr_get(x_388, 0);
lean::inc(x_389);
x_391 = lean::cnstr_get(x_388, 1);
lean::inc(x_391);
x_393 = lean::cnstr_get(x_388, 2);
lean::inc(x_393);
lean::dec(x_388);
x_396 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_391);
if (lean::obj_tag(x_396) == 0)
{
obj* x_397; obj* x_399; obj* x_401; obj* x_404; 
x_397 = lean::cnstr_get(x_396, 0);
lean::inc(x_397);
x_399 = lean::cnstr_get(x_396, 1);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_396, 2);
lean::inc(x_401);
lean::dec(x_396);
x_404 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_399);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; obj* x_407; obj* x_409; obj* x_412; 
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_404, 1);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_404, 2);
lean::inc(x_409);
lean::dec(x_404);
x_412 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_407);
if (lean::obj_tag(x_412) == 0)
{
obj* x_413; obj* x_415; obj* x_417; obj* x_420; obj* x_421; obj* x_424; obj* x_425; obj* x_428; obj* x_431; obj* x_432; obj* x_435; obj* x_438; uint32 x_441; uint32 x_443; uint8 x_444; 
x_413 = lean::cnstr_get(x_412, 0);
lean::inc(x_413);
x_415 = lean::cnstr_get(x_412, 1);
lean::inc(x_415);
x_417 = lean::cnstr_get(x_412, 2);
lean::inc(x_417);
lean::dec(x_412);
x_420 = lean::mk_nat_obj(4096u);
x_421 = lean::nat_mul(x_389, x_420);
lean::dec(x_420);
lean::dec(x_389);
x_424 = lean::mk_nat_obj(256u);
x_425 = lean::nat_mul(x_397, x_424);
lean::dec(x_424);
lean::dec(x_397);
x_428 = lean::nat_add(x_421, x_425);
lean::dec(x_425);
lean::dec(x_421);
x_431 = lean::mk_nat_obj(16u);
x_432 = lean::nat_mul(x_405, x_431);
lean::dec(x_431);
lean::dec(x_405);
x_435 = lean::nat_add(x_428, x_432);
lean::dec(x_432);
lean::dec(x_428);
x_438 = lean::nat_add(x_435, x_413);
lean::dec(x_413);
lean::dec(x_435);
x_441 = lean::uint32_of_nat(x_438);
lean::dec(x_438);
x_443 = 55296;
x_444 = x_441 < x_443;
if (x_444 == 0)
{
uint32 x_445; uint8 x_446; 
x_445 = 57343;
x_446 = x_445 < x_441;
if (x_446 == 0)
{
uint32 x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; 
x_447 = 0;
x_448 = lean::string_push(x_1, x_447);
x_449 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_448, x_415);
x_450 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_449);
x_451 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_450);
x_452 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_451);
x_453 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_452);
x_454 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_453);
x_455 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_454);
x_456 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_455);
x_457 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_456);
x_458 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_457);
x_459 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_458);
return x_459;
}
else
{
uint32 x_460; uint8 x_461; 
x_460 = 1114112;
x_461 = x_441 < x_460;
if (x_461 == 0)
{
uint32 x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
x_462 = 0;
x_463 = lean::string_push(x_1, x_462);
x_464 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_463, x_415);
x_465 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_464);
x_466 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_465);
x_467 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_466);
x_468 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_467);
x_469 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_468);
x_470 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_469);
x_471 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_470);
x_472 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_471);
x_473 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_472);
x_474 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_473);
return x_474;
}
else
{
obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; 
x_475 = lean::string_push(x_1, x_441);
x_476 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_475, x_415);
x_477 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_476);
x_478 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_477);
x_479 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_478);
x_480 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_479);
x_481 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_480);
x_482 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_481);
x_483 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_482);
x_484 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_483);
x_485 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_484);
x_486 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_485);
return x_486;
}
}
}
else
{
obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_498; 
x_487 = lean::string_push(x_1, x_441);
x_488 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_487, x_415);
x_489 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_488);
x_490 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_489);
x_491 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_490);
x_492 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_491);
x_493 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_492);
x_494 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_493);
x_495 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_494);
x_496 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_495);
x_497 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_496);
x_498 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_497);
return x_498;
}
}
else
{
obj* x_504; uint8 x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_389);
lean::dec(x_405);
lean::dec(x_397);
x_504 = lean::cnstr_get(x_412, 0);
lean::inc(x_504);
x_506 = lean::cnstr_get_scalar<uint8>(x_412, sizeof(void*)*1);
if (lean::is_shared(x_412)) {
 lean::dec(x_412);
 x_507 = lean::box(0);
} else {
 lean::cnstr_release(x_412, 0);
 x_507 = x_412;
}
if (lean::is_scalar(x_507)) {
 x_508 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_508 = x_507;
}
lean::cnstr_set(x_508, 0, x_504);
lean::cnstr_set_scalar(x_508, sizeof(void*)*1, x_506);
x_509 = x_508;
x_510 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_509);
x_511 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_510);
x_512 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_511);
x_513 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_512);
x_514 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_513);
x_515 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_514);
x_516 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_515);
x_517 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_516);
x_518 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_517);
return x_518;
}
}
else
{
obj* x_523; uint8 x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; obj* x_531; obj* x_532; obj* x_533; obj* x_534; obj* x_535; obj* x_536; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_389);
lean::dec(x_397);
x_523 = lean::cnstr_get(x_404, 0);
lean::inc(x_523);
x_525 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*1);
if (lean::is_shared(x_404)) {
 lean::dec(x_404);
 x_526 = lean::box(0);
} else {
 lean::cnstr_release(x_404, 0);
 x_526 = x_404;
}
if (lean::is_scalar(x_526)) {
 x_527 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_527 = x_526;
}
lean::cnstr_set(x_527, 0, x_523);
lean::cnstr_set_scalar(x_527, sizeof(void*)*1, x_525);
x_528 = x_527;
x_529 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_528);
x_530 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_529);
x_531 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_530);
x_532 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_531);
x_533 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_532);
x_534 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_533);
x_535 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_534);
x_536 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_535);
return x_536;
}
}
else
{
obj* x_540; uint8 x_542; obj* x_543; obj* x_544; obj* x_545; obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_389);
x_540 = lean::cnstr_get(x_396, 0);
lean::inc(x_540);
x_542 = lean::cnstr_get_scalar<uint8>(x_396, sizeof(void*)*1);
if (lean::is_shared(x_396)) {
 lean::dec(x_396);
 x_543 = lean::box(0);
} else {
 lean::cnstr_release(x_396, 0);
 x_543 = x_396;
}
if (lean::is_scalar(x_543)) {
 x_544 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_544 = x_543;
}
lean::cnstr_set(x_544, 0, x_540);
lean::cnstr_set_scalar(x_544, sizeof(void*)*1, x_542);
x_545 = x_544;
x_546 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_545);
x_547 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_546);
x_548 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_547);
x_549 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_548);
x_550 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_549);
x_551 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_550);
x_552 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_551);
return x_552;
}
}
else
{
obj* x_555; uint8 x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; 
lean::dec(x_1);
lean::dec(x_7);
x_555 = lean::cnstr_get(x_388, 0);
lean::inc(x_555);
x_557 = lean::cnstr_get_scalar<uint8>(x_388, sizeof(void*)*1);
if (lean::is_shared(x_388)) {
 lean::dec(x_388);
 x_558 = lean::box(0);
} else {
 lean::cnstr_release(x_388, 0);
 x_558 = x_388;
}
if (lean::is_scalar(x_558)) {
 x_559 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_559 = x_558;
}
lean::cnstr_set(x_559, 0, x_555);
lean::cnstr_set_scalar(x_559, sizeof(void*)*1, x_557);
x_560 = x_559;
x_561 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_385, x_560);
x_562 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_561);
x_563 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_562);
x_564 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_563);
x_565 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_564);
x_566 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_565);
return x_566;
}
}
else
{
obj* x_569; uint8 x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; 
lean::dec(x_1);
lean::dec(x_7);
x_569 = lean::cnstr_get(x_382, 0);
lean::inc(x_569);
x_571 = lean::cnstr_get_scalar<uint8>(x_382, sizeof(void*)*1);
if (lean::is_shared(x_382)) {
 lean::dec(x_382);
 x_572 = lean::box(0);
} else {
 lean::cnstr_release(x_382, 0);
 x_572 = x_382;
}
if (lean::is_scalar(x_572)) {
 x_573 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_573 = x_572;
}
lean::cnstr_set(x_573, 0, x_569);
lean::cnstr_set_scalar(x_573, sizeof(void*)*1, x_571);
x_574 = x_573;
x_575 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_211, x_574);
x_576 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_575);
x_577 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_576);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_577);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_578);
return x_579;
}
}
else
{
obj* x_584; obj* x_585; obj* x_586; obj* x_587; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_211);
x_584 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_210);
x_585 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_584);
x_586 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_585);
x_587 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_586);
return x_587;
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
obj* x_589; obj* x_591; 
lean::dec(x_0);
x_589 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_589);
x_591 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_591, 0, x_1);
lean::cnstr_set(x_591, 1, x_2);
lean::cnstr_set(x_591, 2, x_589);
return x_591;
}
}
}
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_3__parse__mangled__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_1, x_2, x_0);
x_5 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_5);
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_4);
return x_7;
}
}
obj* _init_l_lean_string_demangle___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_name__mangling_3__parse__mangled__string), 1, 0);
return x_0;
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
obj* _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_s");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main(obj* x_0, obj* x_1) {
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
x_8 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_3);
x_9 = l_lean_string_mangle(x_5);
x_10 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::string_length(x_9);
x_13 = l_nat_repr(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
x_16 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2;
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
x_25 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_20);
x_26 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2;
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
obj* l___private_init_lean_name__mangling_4__name_mangle__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_name_mangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_1, x_0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(uint32 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::string_iterator_has_next(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_9);
return x_12;
}
else
{
uint32 x_13; uint8 x_14; 
x_13 = lean::string_iterator_curr(x_1);
x_14 = x_13 == x_0;
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
x_15 = l_char_quote__core(x_13);
x_16 = l_char_has__repr___closed__1;
lean::inc(x_16);
x_18 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_20 = lean::string_append(x_18, x_16);
x_21 = lean::box(0);
x_22 = l_mjoin___rarg___closed__1;
lean::inc(x_21);
lean::inc(x_22);
x_25 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_20, x_22, x_21, x_21, x_1);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::string_iterator_next(x_1);
x_30 = lean::box(0);
x_31 = lean::box_uint32(x_13);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_30);
return x_32;
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__5(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__7(x_5, x_4, x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = lean::string_push(x_4, x_2);
x_7 = lean::string_iterator_remaining(x_1);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__9(x_7, x_6, x_1);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; uint32 x_19; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_11, 2);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::unbox_uint32(x_12);
lean::dec(x_12);
x_21 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_19, x_14);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_21);
return x_22;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_11, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_26 = x_11;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
return x_28;
}
}
else
{
uint32 x_29; uint8 x_30; 
x_29 = lean::string_iterator_curr(x_0);
x_30 = l_char_is__digit(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_44; 
x_31 = l_char_quote__core(x_29);
x_32 = l_char_has__repr___closed__1;
lean::inc(x_32);
x_34 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_36 = lean::string_append(x_34, x_32);
x_37 = lean::box(0);
x_38 = l_mjoin___rarg___closed__1;
lean::inc(x_37);
lean::inc(x_38);
x_41 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_36, x_38, x_37, x_37, x_0);
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_42);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_41);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_47; obj* x_49; uint32 x_52; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 2);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::unbox_uint32(x_45);
lean::dec(x_45);
x_54 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_52, x_47);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_54);
return x_55;
}
else
{
obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = lean::cnstr_get(x_44, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (lean::is_shared(x_44)) {
 lean::dec(x_44);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_44, 0);
 x_59 = x_44;
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_58);
x_61 = x_60;
return x_61;
}
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::inc(x_0);
x_63 = lean::string_iterator_next(x_0);
x_64 = lean::box(0);
x_65 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_63);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_65);
return x_66;
}
}
}
}
obj* l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(x_0);
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
obj* x_14; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_7; 
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = l___private_init_lean_parser_parsec_2__take__aux___main___rarg(x_0, x_5, x_1);
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
obj* l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; 
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
obj* _init_l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1() {
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
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; obj* x_7; uint32 x_10; uint32 x_11; uint8 x_12; obj* x_14; uint32 x_15; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = 95;
x_11 = 55296;
x_12 = x_10 < x_11;
lean::inc(x_2);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
if (x_12 == 0)
{
uint32 x_17; uint8 x_18; 
x_17 = 57343;
x_18 = x_17 < x_10;
if (x_18 == 0)
{
uint32 x_19; 
x_19 = 0;
x_15 = x_19;
goto lbl_16;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = 1114112;
x_21 = x_10 < x_20;
if (x_21 == 0)
{
uint32 x_22; 
x_22 = 0;
x_15 = x_22;
goto lbl_16;
}
else
{
x_15 = x_10;
goto lbl_16;
}
}
}
else
{
x_15 = x_10;
goto lbl_16;
}
lbl_16:
{
obj* x_23; 
if (lean::obj_tag(x_14) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_14, 2);
lean::inc(x_27);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_29 = x_14;
}
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_1);
if (lean::is_scalar(x_29)) {
 x_33 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_33 = x_29;
}
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_25);
lean::cnstr_set(x_33, 2, x_30);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_33);
x_23 = x_34;
goto lbl_24;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_14, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_38 = x_14;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
x_23 = x_40;
goto lbl_24;
}
lbl_24:
{
if (lean::obj_tag(x_23) == 0)
{
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
return x_23;
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; uint8 x_49; 
x_44 = lean::cnstr_get(x_23, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_46 == 0)
{
obj* x_52; obj* x_53; obj* x_57; 
lean::dec(x_23);
x_52 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_53 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_53);
lean::inc(x_52);
x_57 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_52, x_53, x_2);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; obj* x_63; 
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 2);
lean::inc(x_60);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 lean::cnstr_release(x_57, 2);
 x_62 = x_57;
}
x_63 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_58);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_68; uint32 x_71; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_63, 2);
lean::inc(x_68);
lean::dec(x_63);
if (x_12 == 0)
{
uint32 x_73; uint8 x_74; 
x_73 = 57343;
x_74 = x_73 < x_10;
if (x_74 == 0)
{
uint32 x_75; 
x_75 = 0;
x_71 = x_75;
goto lbl_72;
}
else
{
uint32 x_76; uint8 x_77; 
x_76 = 1114112;
x_77 = x_10 < x_76;
if (x_77 == 0)
{
uint32 x_78; 
x_78 = 0;
x_71 = x_78;
goto lbl_72;
}
else
{
x_71 = x_10;
goto lbl_72;
}
}
}
else
{
x_71 = x_10;
goto lbl_72;
}
lbl_72:
{
obj* x_79; 
x_79 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_71, x_66);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_85; 
x_80 = lean::cnstr_get(x_79, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 2);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_64, x_80);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_96; obj* x_97; 
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 2);
lean::inc(x_90);
lean::dec(x_85);
x_93 = l_lean_string_demangle(x_86);
x_94 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_94);
if (lean::is_scalar(x_62)) {
 x_96 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_96 = x_62;
}
lean::cnstr_set(x_96, 0, x_93);
lean::cnstr_set(x_96, 1, x_88);
lean::cnstr_set(x_96, 2, x_94);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_102; 
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_97, 2);
lean::inc(x_102);
lean::dec(x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_98);
x_106 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_100);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_114 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_110);
return x_114;
}
else
{
obj* x_115; uint8 x_117; 
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
x_47 = x_110;
x_48 = x_115;
x_49 = x_117;
goto lbl_50;
}
}
else
{
obj* x_118; obj* x_122; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_118 = lean::cnstr_get(x_98, 0);
lean::inc(x_118);
lean::dec(x_98);
lean::inc(x_1);
x_122 = lean_name_mk_string(x_1, x_118);
lean::inc(x_7);
x_124 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_122, x_100);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_124);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_132; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_128);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_128, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_128, sizeof(void*)*1);
x_47 = x_128;
x_48 = x_133;
x_49 = x_135;
goto lbl_50;
}
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_97, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_shared(x_97)) {
 lean::dec(x_97);
 x_139 = lean::box(0);
} else {
 lean::cnstr_release(x_97, 0);
 x_139 = x_97;
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_136);
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_138);
x_141 = x_140;
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_141);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_142);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_148; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_148 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_144);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_144, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_144, sizeof(void*)*1);
x_47 = x_144;
x_48 = x_149;
x_49 = x_151;
goto lbl_50;
}
}
}
else
{
obj* x_153; uint8 x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_62);
x_153 = lean::cnstr_get(x_85, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_156 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 x_156 = x_85;
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_153);
lean::cnstr_set_scalar(x_157, sizeof(void*)*1, x_155);
x_158 = x_157;
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_158);
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_165; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_161);
return x_165;
}
else
{
obj* x_166; uint8 x_168; 
x_166 = lean::cnstr_get(x_161, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<uint8>(x_161, sizeof(void*)*1);
x_47 = x_161;
x_48 = x_166;
x_49 = x_168;
goto lbl_50;
}
}
}
else
{
obj* x_171; uint8 x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_64);
lean::dec(x_62);
x_171 = lean::cnstr_get(x_79, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_174 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_174 = x_79;
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_171);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_173);
x_176 = x_175;
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_176);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_177);
if (lean::obj_tag(x_178) == 0)
{
obj* x_182; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_182 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_178);
return x_182;
}
else
{
obj* x_183; uint8 x_185; 
x_183 = lean::cnstr_get(x_178, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
x_47 = x_178;
x_48 = x_183;
x_49 = x_185;
goto lbl_50;
}
}
}
}
else
{
obj* x_187; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_62);
x_187 = lean::cnstr_get(x_63, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_190 = x_63;
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_187);
lean::cnstr_set_scalar(x_191, sizeof(void*)*1, x_189);
x_192 = x_191;
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_192);
if (lean::obj_tag(x_193) == 0)
{
obj* x_197; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_197 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_193);
return x_197;
}
else
{
obj* x_198; uint8 x_200; 
x_198 = lean::cnstr_get(x_193, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get_scalar<uint8>(x_193, sizeof(void*)*1);
x_47 = x_193;
x_48 = x_198;
x_49 = x_200;
goto lbl_50;
}
}
}
else
{
obj* x_201; uint8 x_203; obj* x_204; obj* x_206; obj* x_207; 
x_201 = lean::cnstr_get(x_57, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_204 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 x_204 = x_57;
}
lean::inc(x_201);
if (lean::is_scalar(x_204)) {
 x_206 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_206 = x_204;
}
lean::cnstr_set(x_206, 0, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*1, x_203);
x_207 = x_206;
x_47 = x_207;
x_48 = x_201;
x_49 = x_203;
goto lbl_50;
}
}
else
{
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_44);
return x_23;
}
lbl_50:
{
if (x_49 == 0)
{
obj* x_213; 
lean::dec(x_47);
x_213 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_15, x_2);
if (lean::obj_tag(x_213) == 0)
{
obj* x_214; obj* x_216; obj* x_219; 
x_214 = lean::cnstr_get(x_213, 1);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_213, 2);
lean::inc(x_216);
lean::dec(x_213);
x_219 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_214);
if (lean::obj_tag(x_219) == 0)
{
obj* x_220; obj* x_222; obj* x_224; obj* x_227; 
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_219, 2);
lean::inc(x_224);
lean::dec(x_219);
x_227 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_15, x_222);
if (lean::obj_tag(x_227) == 0)
{
obj* x_228; obj* x_230; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_228 = lean::cnstr_get(x_227, 1);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_227, 2);
lean::inc(x_230);
lean::dec(x_227);
x_233 = lean_name_mk_numeral(x_1, x_220);
x_234 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_233, x_228);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_230, x_234);
x_236 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_224, x_235);
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_216, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_238);
return x_239;
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_220);
lean::dec(x_1);
lean::dec(x_7);
x_243 = lean::cnstr_get(x_227, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get_scalar<uint8>(x_227, sizeof(void*)*1);
if (lean::is_shared(x_227)) {
 lean::dec(x_227);
 x_246 = lean::box(0);
} else {
 lean::cnstr_release(x_227, 0);
 x_246 = x_227;
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_243);
lean::cnstr_set_scalar(x_247, sizeof(void*)*1, x_245);
x_248 = x_247;
x_249 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_224, x_248);
x_250 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_216, x_249);
x_251 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_250);
x_252 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_251);
return x_252;
}
}
else
{
obj* x_255; uint8 x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_1);
lean::dec(x_7);
x_255 = lean::cnstr_get(x_219, 0);
lean::inc(x_255);
x_257 = lean::cnstr_get_scalar<uint8>(x_219, sizeof(void*)*1);
if (lean::is_shared(x_219)) {
 lean::dec(x_219);
 x_258 = lean::box(0);
} else {
 lean::cnstr_release(x_219, 0);
 x_258 = x_219;
}
if (lean::is_scalar(x_258)) {
 x_259 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_259 = x_258;
}
lean::cnstr_set(x_259, 0, x_255);
lean::cnstr_set_scalar(x_259, sizeof(void*)*1, x_257);
x_260 = x_259;
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_216, x_260);
x_262 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_261);
x_263 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_262);
return x_263;
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_1);
lean::dec(x_7);
x_266 = lean::cnstr_get(x_213, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_213, sizeof(void*)*1);
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 x_269 = x_213;
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_271);
x_273 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_272);
return x_273;
}
}
else
{
obj* x_278; 
lean::dec(x_48);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_278 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_44, x_47);
return x_278;
}
}
}
}
}
}
else
{
obj* x_280; obj* x_282; 
lean::dec(x_0);
x_280 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_280);
x_282 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_282, 0, x_1);
lean::cnstr_set(x_282, 1, x_2);
lean::cnstr_set(x_282, 2, x_280);
return x_282;
}
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_6__parse__mangled__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = l_string_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_0, x_4, x_1);
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
x_13 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_11, x_12, x_6);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_14);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_13);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
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
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_name__mangling_6__parse__mangled__name), 2, 1);
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
 l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1();
 l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2();
 l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3 = _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3();
 l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1 = _init_l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1();
 l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1 = _init_l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1();
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1();
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2();
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3();
 l_lean_string_demangle___closed__1 = _init_l_lean_string_demangle___closed__1();
 l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1();
 l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2();
 l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1();
}
