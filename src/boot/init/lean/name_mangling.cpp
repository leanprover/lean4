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
uint8 l_char_is__digit(uint32);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
uint32 l_char_of__nat(obj*);
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
obj* x_6; obj* x_7; uint32 x_10; obj* x_11; uint8 x_13; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::string_iterator_curr(x_1);
x_13 = l_char_is__alpha(x_10);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = l_char_is__digit(x_10);
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 95;
x_16 = x_10 == x_15;
if (x_16 == 0)
{
obj* x_17; 
x_17 = lean::box(0);
x_11 = x_17;
goto lbl_12;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::string_iterator_next(x_1);
x_19 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_20 = lean::string_append(x_2, x_19);
x_0 = x_7;
x_1 = x_18;
x_2 = x_20;
goto _start;
}
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
else
{
if (x_13 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 95;
x_26 = x_10 == x_25;
if (x_26 == 0)
{
obj* x_27; 
x_27 = lean::box(0);
x_11 = x_27;
goto lbl_12;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::string_iterator_next(x_1);
x_29 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_30 = lean::string_append(x_2, x_29);
x_0 = x_7;
x_1 = x_28;
x_2 = x_30;
goto _start;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::string_iterator_next(x_1);
x_33 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_32;
x_2 = x_33;
goto _start;
}
}
lbl_12:
{
obj* x_36; obj* x_37; uint8 x_38; 
lean::dec(x_11);
x_36 = lean::uint32_to_nat(x_10);
x_37 = lean::mk_nat_obj(255u);
x_38 = lean::nat_dec_lt(x_36, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; uint32 x_44; obj* x_45; obj* x_46; obj* x_49; obj* x_50; uint32 x_51; obj* x_52; obj* x_53; obj* x_56; obj* x_57; uint32 x_58; obj* x_59; obj* x_60; uint32 x_63; obj* x_64; obj* x_65; 
x_40 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_41 = lean::string_append(x_2, x_40);
x_42 = lean::mk_nat_obj(4096u);
x_43 = lean::nat_div(x_36, x_42);
x_44 = l_nat_digit__char(x_43);
x_45 = lean::string_push(x_41, x_44);
x_46 = lean::nat_mod(x_36, x_42);
lean::dec(x_42);
lean::dec(x_36);
x_49 = lean::mk_nat_obj(256u);
x_50 = lean::nat_div(x_46, x_49);
x_51 = l_nat_digit__char(x_50);
x_52 = lean::string_push(x_45, x_51);
x_53 = lean::nat_mod(x_46, x_49);
lean::dec(x_49);
lean::dec(x_46);
x_56 = lean::mk_nat_obj(16u);
x_57 = lean::nat_div(x_53, x_56);
x_58 = l_nat_digit__char(x_57);
x_59 = lean::string_push(x_52, x_58);
x_60 = lean::nat_mod(x_53, x_56);
lean::dec(x_56);
lean::dec(x_53);
x_63 = l_nat_digit__char(x_60);
x_64 = lean::string_push(x_59, x_63);
x_65 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_65;
x_2 = x_64;
goto _start;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; uint32 x_71; obj* x_72; obj* x_73; uint32 x_76; obj* x_77; obj* x_78; 
x_67 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_68 = lean::string_append(x_2, x_67);
x_69 = lean::mk_nat_obj(16u);
x_70 = lean::nat_div(x_36, x_69);
x_71 = l_nat_digit__char(x_70);
x_72 = lean::string_push(x_68, x_71);
x_73 = lean::nat_mod(x_36, x_69);
lean::dec(x_69);
lean::dec(x_36);
x_76 = l_nat_digit__char(x_73);
x_77 = lean::string_push(x_72, x_76);
x_78 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_78;
x_2 = x_77;
goto _start;
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
obj* x_11; obj* x_12; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
x_11 = lean::box(0);
x_12 = l_string_join___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_1);
lean::cnstr_set(x_14, 3, x_11);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = x_16;
return x_17;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_9, 0);
lean::inc(x_20);
lean::dec(x_9);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set(x_24, 2, x_23);
return x_24;
}
}
else
{
obj* x_27; obj* x_28; obj* x_31; 
lean::dec(x_1);
lean::dec(x_0);
x_27 = l_string_join___closed__1;
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_28);
lean::inc(x_27);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_28);
return x_31;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_8);
x_10 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = lean::string_iterator_curr(x_0);
x_12 = l_char_is__digit(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
x_13 = l_char_quote__core(x_11);
x_14 = l_char_has__repr___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = lean::string_append(x_16, x_14);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_18, x_20, x_19, x_19, x_0);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_22);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::string_iterator_next(x_0);
x_27 = lean::box(0);
x_28 = lean::box_uint32(x_11);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_27);
return x_29;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
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
x_17 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_18 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_9);
lean::cnstr_set(x_22, 2, x_20);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_27; 
lean::dec(x_0);
x_25 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_25);
x_27 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_23, x_25);
return x_27;
}
else
{
obj* x_28; uint8 x_30; 
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
x_1 = x_23;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_6, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_34 = x_6;
}
lean::inc(x_31);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_33);
x_37 = x_36;
x_1 = x_37;
x_2 = x_31;
x_3 = x_33;
goto lbl_4;
}
lbl_4:
{
obj* x_38; obj* x_39; uint8 x_40; 
if (x_3 == 0)
{
obj* x_43; uint8 x_45; 
lean::dec(x_1);
x_45 = lean::string_iterator_has_next(x_0);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_52; 
x_46 = lean::box(0);
x_47 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_48 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_48);
lean::inc(x_47);
x_52 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_47, x_48, x_46, x_46, x_0);
x_43 = x_52;
goto lbl_44;
}
else
{
uint32 x_53; uint32 x_54; uint8 x_55; uint8 x_57; 
x_53 = lean::string_iterator_curr(x_0);
x_54 = 97;
x_57 = x_54 <= x_53;
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_68; 
x_58 = l_char_quote__core(x_53);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_65);
x_68 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_63, x_65, x_64, x_64, x_0);
x_43 = x_68;
goto lbl_44;
}
else
{
uint8 x_69; 
x_69 = 1;
x_55 = x_69;
goto lbl_56;
}
lbl_56:
{
uint32 x_70; uint8 x_71; 
x_70 = 102;
x_71 = x_53 <= x_70;
if (x_71 == 0)
{
obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_82; 
x_72 = l_char_quote__core(x_53);
x_73 = l_char_has__repr___closed__1;
lean::inc(x_73);
x_75 = lean::string_append(x_73, x_72);
lean::dec(x_72);
x_77 = lean::string_append(x_75, x_73);
x_78 = lean::box(0);
x_79 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_79);
x_82 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_77, x_79, x_78, x_78, x_0);
x_43 = x_82;
goto lbl_44;
}
else
{
if (x_55 == 0)
{
obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_93; 
x_83 = l_char_quote__core(x_53);
x_84 = l_char_has__repr___closed__1;
lean::inc(x_84);
x_86 = lean::string_append(x_84, x_83);
lean::dec(x_83);
x_88 = lean::string_append(x_86, x_84);
x_89 = lean::box(0);
x_90 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_90);
x_93 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_88, x_90, x_89, x_89, x_0);
x_43 = x_93;
goto lbl_44;
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::inc(x_0);
x_95 = lean::string_iterator_next(x_0);
x_96 = lean::box(0);
x_97 = lean::box_uint32(x_53);
x_98 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set(x_98, 2, x_96);
x_43 = x_98;
goto lbl_44;
}
}
}
}
lbl_44:
{
obj* x_99; obj* x_101; 
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_99, x_43);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; uint32 x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_120; obj* x_121; 
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 2);
lean::inc(x_106);
if (lean::is_shared(x_101)) {
 lean::dec(x_101);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 lean::cnstr_release(x_101, 2);
 x_108 = x_101;
}
x_109 = lean::unbox_uint32(x_102);
lean::dec(x_102);
x_111 = lean::uint32_to_nat(x_109);
x_112 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_113 = lean::nat_sub(x_111, x_112);
lean::dec(x_111);
x_115 = lean::mk_nat_obj(10u);
x_116 = lean::nat_add(x_115, x_113);
lean::dec(x_113);
lean::dec(x_115);
lean::inc(x_99);
if (lean::is_scalar(x_108)) {
 x_120 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_120 = x_108;
}
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set(x_120, 1, x_104);
lean::cnstr_set(x_120, 2, x_99);
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_106, x_120);
if (lean::obj_tag(x_121) == 0)
{
obj* x_123; obj* x_124; obj* x_126; 
lean::dec(x_0);
x_123 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_121);
x_124 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_124);
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_123, x_124);
return x_126;
}
else
{
obj* x_127; uint8 x_129; 
x_127 = lean::cnstr_get(x_121, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
x_38 = x_121;
x_39 = x_127;
x_40 = x_129;
goto lbl_41;
}
}
else
{
obj* x_130; uint8 x_132; obj* x_133; obj* x_135; obj* x_136; 
x_130 = lean::cnstr_get(x_101, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_shared(x_101)) {
 lean::dec(x_101);
 x_133 = lean::box(0);
} else {
 lean::cnstr_release(x_101, 0);
 x_133 = x_101;
}
lean::inc(x_130);
if (lean::is_scalar(x_133)) {
 x_135 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_135 = x_133;
}
lean::cnstr_set(x_135, 0, x_130);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_132);
x_136 = x_135;
x_38 = x_136;
x_39 = x_130;
x_40 = x_132;
goto lbl_41;
}
}
}
else
{
obj* x_139; obj* x_141; 
lean::dec(x_0);
lean::dec(x_2);
x_139 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_139);
x_141 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_139);
return x_141;
}
lbl_41:
{
if (x_40 == 0)
{
obj* x_143; uint8 x_145; 
lean::dec(x_38);
x_145 = lean::string_iterator_has_next(x_0);
if (x_145 == 0)
{
obj* x_146; obj* x_147; obj* x_148; obj* x_151; 
x_146 = lean::box(0);
x_147 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_148 = l_mjoin___rarg___closed__1;
lean::inc(x_148);
lean::inc(x_147);
x_151 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_147, x_148, x_146, x_146, x_0);
x_143 = x_151;
goto lbl_144;
}
else
{
uint32 x_152; uint32 x_153; uint8 x_154; uint8 x_156; 
x_152 = lean::string_iterator_curr(x_0);
x_153 = 65;
x_156 = x_153 <= x_152;
if (x_156 == 0)
{
obj* x_157; obj* x_158; obj* x_160; obj* x_162; obj* x_163; obj* x_164; obj* x_166; 
x_157 = l_char_quote__core(x_152);
x_158 = l_char_has__repr___closed__1;
lean::inc(x_158);
x_160 = lean::string_append(x_158, x_157);
lean::dec(x_157);
x_162 = lean::string_append(x_160, x_158);
x_163 = lean::box(0);
x_164 = l_mjoin___rarg___closed__1;
lean::inc(x_164);
x_166 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_162, x_164, x_163, x_163, x_0);
x_143 = x_166;
goto lbl_144;
}
else
{
uint8 x_167; 
x_167 = 1;
x_154 = x_167;
goto lbl_155;
}
lbl_155:
{
uint32 x_168; uint8 x_169; 
x_168 = 70;
x_169 = x_152 <= x_168;
if (x_169 == 0)
{
obj* x_170; obj* x_171; obj* x_173; obj* x_175; obj* x_176; obj* x_177; obj* x_179; 
x_170 = l_char_quote__core(x_152);
x_171 = l_char_has__repr___closed__1;
lean::inc(x_171);
x_173 = lean::string_append(x_171, x_170);
lean::dec(x_170);
x_175 = lean::string_append(x_173, x_171);
x_176 = lean::box(0);
x_177 = l_mjoin___rarg___closed__1;
lean::inc(x_177);
x_179 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_175, x_177, x_176, x_176, x_0);
x_143 = x_179;
goto lbl_144;
}
else
{
if (x_154 == 0)
{
obj* x_180; obj* x_181; obj* x_183; obj* x_185; obj* x_186; obj* x_187; obj* x_189; 
x_180 = l_char_quote__core(x_152);
x_181 = l_char_has__repr___closed__1;
lean::inc(x_181);
x_183 = lean::string_append(x_181, x_180);
lean::dec(x_180);
x_185 = lean::string_append(x_183, x_181);
x_186 = lean::box(0);
x_187 = l_mjoin___rarg___closed__1;
lean::inc(x_187);
x_189 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_185, x_187, x_186, x_186, x_0);
x_143 = x_189;
goto lbl_144;
}
else
{
obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_190 = lean::string_iterator_next(x_0);
x_191 = lean::box(0);
x_192 = lean::box_uint32(x_152);
x_193 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_190);
lean::cnstr_set(x_193, 2, x_191);
x_143 = x_193;
goto lbl_144;
}
}
}
}
lbl_144:
{
obj* x_194; obj* x_196; 
x_194 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_194, x_143);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_199; obj* x_201; obj* x_203; uint32 x_204; obj* x_206; obj* x_207; obj* x_208; obj* x_210; obj* x_211; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_221; 
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_196, 2);
lean::inc(x_201);
if (lean::is_shared(x_196)) {
 lean::dec(x_196);
 x_203 = lean::box(0);
} else {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 lean::cnstr_release(x_196, 2);
 x_203 = x_196;
}
x_204 = lean::unbox_uint32(x_197);
lean::dec(x_197);
x_206 = lean::uint32_to_nat(x_204);
x_207 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_208 = lean::nat_sub(x_206, x_207);
lean::dec(x_206);
x_210 = lean::mk_nat_obj(10u);
x_211 = lean::nat_add(x_210, x_208);
lean::dec(x_208);
lean::dec(x_210);
lean::inc(x_194);
if (lean::is_scalar(x_203)) {
 x_215 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_215 = x_203;
}
lean::cnstr_set(x_215, 0, x_211);
lean::cnstr_set(x_215, 1, x_199);
lean::cnstr_set(x_215, 2, x_194);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_201, x_215);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_216);
x_218 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_217);
x_219 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_219);
x_221 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_218, x_219);
return x_221;
}
else
{
obj* x_222; uint8 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_232; 
x_222 = lean::cnstr_get(x_196, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get_scalar<uint8>(x_196, sizeof(void*)*1);
if (lean::is_shared(x_196)) {
 lean::dec(x_196);
 x_225 = lean::box(0);
} else {
 lean::cnstr_release(x_196, 0);
 x_225 = x_196;
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set_scalar(x_226, sizeof(void*)*1, x_224);
x_227 = x_226;
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_227);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_228);
x_230 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_230);
x_232 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_229, x_230);
return x_232;
}
}
}
else
{
obj* x_235; obj* x_236; obj* x_238; 
lean::dec(x_0);
lean::dec(x_39);
x_235 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_38);
x_236 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_236);
x_238 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_235, x_236);
return x_238;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_8);
x_10 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = lean::string_iterator_curr(x_0);
x_12 = l_char_is__alpha(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
x_13 = l_char_quote__core(x_11);
x_14 = l_char_has__repr___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = lean::string_append(x_16, x_14);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_18, x_20, x_19, x_19, x_0);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_22);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::string_iterator_next(x_0);
x_27 = lean::box(0);
x_28 = lean::box_uint32(x_11);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_27);
return x_29;
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
uint32 x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_6 = lean::string_iterator_curr(x_0);
x_7 = l_char_quote__core(x_6);
x_8 = l_char_has__repr___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = lean::string_append(x_10, x_8);
x_13 = lean::box(0);
x_14 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
lean::inc(x_14);
x_16 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_12, x_14, x_13, x_13, x_0);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_23; 
x_20 = lean::box(0);
x_21 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_0);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
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
lean::dec(x_7);
lean::dec(x_1);
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
lean::dec(x_7);
lean::dec(x_1);
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
lean::dec(x_7);
lean::dec(x_1);
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
lean::dec(x_7);
lean::dec(x_1);
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
lean::dec(x_7);
lean::dec(x_1);
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
obj* x_127; obj* x_129; uint32 x_132; obj* x_134; obj* x_136; obj* x_137; 
x_127 = lean::cnstr_get(x_126, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 2);
lean::inc(x_129);
lean::dec(x_126);
x_132 = 95;
lean::inc(x_1);
x_134 = lean::string_push(x_1, x_132);
lean::inc(x_7);
x_136 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_134, x_127);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_136);
if (lean::obj_tag(x_137) == 0)
{
obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_141 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_137);
x_142 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_141);
x_143 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_142);
return x_143;
}
else
{
obj* x_144; uint8 x_146; 
x_144 = lean::cnstr_get(x_137, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get_scalar<uint8>(x_137, sizeof(void*)*1);
x_116 = x_137;
x_117 = x_144;
x_118 = x_146;
goto lbl_119;
}
}
else
{
obj* x_147; uint8 x_149; obj* x_150; obj* x_152; obj* x_153; 
x_147 = lean::cnstr_get(x_126, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_150 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_150 = x_126;
}
lean::inc(x_147);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_147);
lean::cnstr_set_scalar(x_152, sizeof(void*)*1, x_149);
x_153 = x_152;
x_116 = x_153;
x_117 = x_147;
x_118 = x_149;
goto lbl_119;
}
}
else
{
obj* x_158; obj* x_159; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_76);
x_158 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_75);
x_159 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_158);
return x_159;
}
lbl_119:
{
obj* x_160; obj* x_161; uint8 x_162; 
if (x_118 == 0)
{
obj* x_165; obj* x_166; obj* x_170; 
lean::dec(x_116);
x_165 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_166 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_166);
lean::inc(x_165);
x_170 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_165, x_166, x_2);
if (lean::obj_tag(x_170) == 0)
{
obj* x_171; obj* x_173; obj* x_176; 
x_171 = lean::cnstr_get(x_170, 1);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_170, 2);
lean::inc(x_173);
lean::dec(x_170);
x_176 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_184; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 2);
lean::inc(x_181);
lean::dec(x_176);
x_184 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_179);
if (lean::obj_tag(x_184) == 0)
{
obj* x_185; obj* x_187; obj* x_189; obj* x_192; obj* x_193; obj* x_196; uint32 x_199; obj* x_201; obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 2);
lean::inc(x_189);
lean::dec(x_184);
x_192 = lean::mk_nat_obj(16u);
x_193 = lean::nat_mul(x_177, x_192);
lean::dec(x_192);
lean::dec(x_177);
x_196 = lean::nat_add(x_193, x_185);
lean::dec(x_185);
lean::dec(x_193);
x_199 = l_char_of__nat(x_196);
lean::inc(x_1);
x_201 = lean::string_push(x_1, x_199);
lean::inc(x_7);
x_203 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_201, x_187);
x_204 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_203);
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_204);
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_205);
if (lean::obj_tag(x_206) == 0)
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_206);
x_211 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_210);
x_212 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_211);
x_213 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_212);
return x_213;
}
else
{
obj* x_214; uint8 x_216; 
x_214 = lean::cnstr_get(x_206, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get_scalar<uint8>(x_206, sizeof(void*)*1);
x_160 = x_206;
x_161 = x_214;
x_162 = x_216;
goto lbl_163;
}
}
else
{
obj* x_218; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
lean::dec(x_177);
x_218 = lean::cnstr_get(x_184, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_221 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_221 = x_184;
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_218);
lean::cnstr_set_scalar(x_222, sizeof(void*)*1, x_220);
x_223 = x_222;
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_223);
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_224);
if (lean::obj_tag(x_225) == 0)
{
obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_225);
x_230 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_229);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_231);
return x_232;
}
else
{
obj* x_233; uint8 x_235; 
x_233 = lean::cnstr_get(x_225, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get_scalar<uint8>(x_225, sizeof(void*)*1);
x_160 = x_225;
x_161 = x_233;
x_162 = x_235;
goto lbl_163;
}
}
}
else
{
obj* x_236; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
x_236 = lean::cnstr_get(x_176, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_shared(x_176)) {
 lean::dec(x_176);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_176, 0);
 x_239 = x_176;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_236);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_238);
x_241 = x_240;
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_241);
if (lean::obj_tag(x_242) == 0)
{
obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_246 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_242);
x_247 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_246);
x_248 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_247);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_248);
return x_249;
}
else
{
obj* x_250; uint8 x_252; 
x_250 = lean::cnstr_get(x_242, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get_scalar<uint8>(x_242, sizeof(void*)*1);
x_160 = x_242;
x_161 = x_250;
x_162 = x_252;
goto lbl_163;
}
}
}
else
{
obj* x_253; uint8 x_255; obj* x_256; obj* x_258; obj* x_259; 
x_253 = lean::cnstr_get(x_170, 0);
lean::inc(x_253);
x_255 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_shared(x_170)) {
 lean::dec(x_170);
 x_256 = lean::box(0);
} else {
 lean::cnstr_release(x_170, 0);
 x_256 = x_170;
}
lean::inc(x_253);
if (lean::is_scalar(x_256)) {
 x_258 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_258 = x_256;
}
lean::cnstr_set(x_258, 0, x_253);
lean::cnstr_set_scalar(x_258, sizeof(void*)*1, x_255);
x_259 = x_258;
x_160 = x_259;
x_161 = x_253;
x_162 = x_255;
goto lbl_163;
}
}
else
{
obj* x_264; obj* x_265; obj* x_266; 
lean::dec(x_117);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_264 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_116);
x_265 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_264);
x_266 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_265);
return x_266;
}
lbl_163:
{
if (x_162 == 0)
{
obj* x_268; obj* x_269; obj* x_272; 
lean::dec(x_160);
x_268 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_269 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
lean::inc(x_269);
lean::inc(x_268);
x_272 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_268, x_269, x_2);
if (lean::obj_tag(x_272) == 0)
{
obj* x_273; obj* x_275; obj* x_278; 
x_273 = lean::cnstr_get(x_272, 1);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_272, 2);
lean::inc(x_275);
lean::dec(x_272);
x_278 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_273);
if (lean::obj_tag(x_278) == 0)
{
obj* x_279; obj* x_281; obj* x_283; obj* x_286; 
x_279 = lean::cnstr_get(x_278, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_278, 1);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_278, 2);
lean::inc(x_283);
lean::dec(x_278);
x_286 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_281);
if (lean::obj_tag(x_286) == 0)
{
obj* x_287; obj* x_289; obj* x_291; obj* x_294; 
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_286, 2);
lean::inc(x_291);
lean::dec(x_286);
x_294 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_289);
if (lean::obj_tag(x_294) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_302; 
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_294, 2);
lean::inc(x_299);
lean::dec(x_294);
x_302 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_297);
if (lean::obj_tag(x_302) == 0)
{
obj* x_303; obj* x_305; obj* x_307; obj* x_310; obj* x_311; obj* x_314; obj* x_315; obj* x_318; obj* x_321; obj* x_322; obj* x_325; obj* x_328; uint32 x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
x_303 = lean::cnstr_get(x_302, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_302, 1);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_302, 2);
lean::inc(x_307);
lean::dec(x_302);
x_310 = lean::mk_nat_obj(4096u);
x_311 = lean::nat_mul(x_279, x_310);
lean::dec(x_310);
lean::dec(x_279);
x_314 = lean::mk_nat_obj(256u);
x_315 = lean::nat_mul(x_287, x_314);
lean::dec(x_314);
lean::dec(x_287);
x_318 = lean::nat_add(x_311, x_315);
lean::dec(x_315);
lean::dec(x_311);
x_321 = lean::mk_nat_obj(16u);
x_322 = lean::nat_mul(x_295, x_321);
lean::dec(x_321);
lean::dec(x_295);
x_325 = lean::nat_add(x_318, x_322);
lean::dec(x_322);
lean::dec(x_318);
x_328 = lean::nat_add(x_325, x_303);
lean::dec(x_303);
lean::dec(x_325);
x_331 = l_char_of__nat(x_328);
x_332 = lean::string_push(x_1, x_331);
x_333 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_7, x_332, x_305);
x_334 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_307, x_333);
x_335 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_299, x_334);
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_335);
x_337 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_336);
x_338 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_337);
x_339 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_338);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_339);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_340);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_341);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_342);
return x_343;
}
else
{
obj* x_349; uint8 x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_295);
lean::dec(x_287);
lean::dec(x_279);
x_349 = lean::cnstr_get(x_302, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get_scalar<uint8>(x_302, sizeof(void*)*1);
if (lean::is_shared(x_302)) {
 lean::dec(x_302);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_302, 0);
 x_352 = x_302;
}
if (lean::is_scalar(x_352)) {
 x_353 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_353 = x_352;
}
lean::cnstr_set(x_353, 0, x_349);
lean::cnstr_set_scalar(x_353, sizeof(void*)*1, x_351);
x_354 = x_353;
x_355 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_299, x_354);
x_356 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_355);
x_357 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_356);
x_358 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_357);
x_359 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_358);
x_360 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_359);
x_361 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_360);
x_362 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_361);
x_363 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_362);
return x_363;
}
}
else
{
obj* x_368; uint8 x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_287);
lean::dec(x_279);
x_368 = lean::cnstr_get(x_294, 0);
lean::inc(x_368);
x_370 = lean::cnstr_get_scalar<uint8>(x_294, sizeof(void*)*1);
if (lean::is_shared(x_294)) {
 lean::dec(x_294);
 x_371 = lean::box(0);
} else {
 lean::cnstr_release(x_294, 0);
 x_371 = x_294;
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_368);
lean::cnstr_set_scalar(x_372, sizeof(void*)*1, x_370);
x_373 = x_372;
x_374 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_373);
x_375 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_374);
x_376 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_375);
x_377 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_376);
x_378 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_377);
x_379 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_378);
x_380 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_379);
x_381 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_380);
return x_381;
}
}
else
{
obj* x_385; uint8 x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_279);
x_385 = lean::cnstr_get(x_286, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get_scalar<uint8>(x_286, sizeof(void*)*1);
if (lean::is_shared(x_286)) {
 lean::dec(x_286);
 x_388 = lean::box(0);
} else {
 lean::cnstr_release(x_286, 0);
 x_388 = x_286;
}
if (lean::is_scalar(x_388)) {
 x_389 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_389 = x_388;
}
lean::cnstr_set(x_389, 0, x_385);
lean::cnstr_set_scalar(x_389, sizeof(void*)*1, x_387);
x_390 = x_389;
x_391 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_390);
x_392 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_391);
x_393 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_392);
x_394 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_393);
x_395 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_394);
x_396 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_395);
x_397 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_396);
return x_397;
}
}
else
{
obj* x_400; uint8 x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; 
lean::dec(x_7);
lean::dec(x_1);
x_400 = lean::cnstr_get(x_278, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get_scalar<uint8>(x_278, sizeof(void*)*1);
if (lean::is_shared(x_278)) {
 lean::dec(x_278);
 x_403 = lean::box(0);
} else {
 lean::cnstr_release(x_278, 0);
 x_403 = x_278;
}
if (lean::is_scalar(x_403)) {
 x_404 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_404 = x_403;
}
lean::cnstr_set(x_404, 0, x_400);
lean::cnstr_set_scalar(x_404, sizeof(void*)*1, x_402);
x_405 = x_404;
x_406 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_405);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_407);
x_409 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_408);
x_410 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_409);
x_411 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_410);
return x_411;
}
}
else
{
obj* x_414; uint8 x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
lean::dec(x_7);
lean::dec(x_1);
x_414 = lean::cnstr_get(x_272, 0);
lean::inc(x_414);
x_416 = lean::cnstr_get_scalar<uint8>(x_272, sizeof(void*)*1);
if (lean::is_shared(x_272)) {
 lean::dec(x_272);
 x_417 = lean::box(0);
} else {
 lean::cnstr_release(x_272, 0);
 x_417 = x_272;
}
if (lean::is_scalar(x_417)) {
 x_418 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_418 = x_417;
}
lean::cnstr_set(x_418, 0, x_414);
lean::cnstr_set_scalar(x_418, sizeof(void*)*1, x_416);
x_419 = x_418;
x_420 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_161, x_419);
x_421 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_420);
x_422 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_421);
x_423 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_422);
x_424 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_423);
return x_424;
}
}
else
{
obj* x_429; obj* x_430; obj* x_431; obj* x_432; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_161);
x_429 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_117, x_160);
x_430 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_429);
x_431 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_430);
x_432 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_431);
return x_432;
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
obj* x_434; obj* x_436; 
lean::dec(x_0);
x_434 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_434);
x_436 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_436, 0, x_1);
lean::cnstr_set(x_436, 1, x_2);
lean::cnstr_set(x_436, 2, x_434);
return x_436;
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
return x_0;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_2);
x_8 = l_lean_string_mangle(x_4);
x_9 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_10 = lean::string_append(x_7, x_9);
x_11 = lean::string_length(x_8);
x_12 = l_nat_repr(x_11);
x_13 = lean::string_append(x_10, x_12);
lean::dec(x_12);
x_15 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2;
x_16 = lean::string_append(x_13, x_15);
x_17 = lean::string_append(x_16, x_8);
lean::dec(x_8);
return x_17;
}
default:
{
obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::dec(x_1);
x_24 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_19);
x_25 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2;
x_26 = lean::string_append(x_24, x_25);
x_27 = l_nat_repr(x_21);
x_28 = lean::string_append(x_26, x_27);
lean::dec(x_27);
x_30 = lean::string_append(x_28, x_25);
return x_30;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = lean::string_iterator_curr(x_1);
x_13 = x_12 == x_0;
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; 
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_21);
x_23 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_19, x_21, x_20, x_20, x_1);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_23);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::string_iterator_next(x_1);
x_28 = lean::box(0);
x_29 = lean::box_uint32(x_12);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_28);
return x_30;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_8);
x_10 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 2);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::unbox_uint32(x_11);
lean::dec(x_11);
x_20 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_18, x_13);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_20);
return x_21;
}
else
{
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_10, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_25 = x_10;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_24);
x_27 = x_26;
return x_27;
}
}
else
{
uint32 x_28; uint8 x_29; 
x_28 = lean::string_iterator_curr(x_0);
x_29 = l_char_is__digit(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; 
x_30 = l_char_quote__core(x_28);
x_31 = l_char_has__repr___closed__1;
lean::inc(x_31);
x_33 = lean::string_append(x_31, x_30);
lean::dec(x_30);
x_35 = lean::string_append(x_33, x_31);
x_36 = lean::box(0);
x_37 = l_mjoin___rarg___closed__1;
lean::inc(x_37);
x_39 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_35, x_37, x_36, x_36, x_0);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; uint32 x_50; obj* x_52; obj* x_53; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 2);
lean::inc(x_47);
lean::dec(x_42);
x_50 = lean::unbox_uint32(x_43);
lean::dec(x_43);
x_52 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_50, x_45);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_52);
return x_53;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_42, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_57 = x_42;
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
return x_59;
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::inc(x_0);
x_61 = lean::string_iterator_next(x_0);
x_62 = lean::box(0);
x_63 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_61);
x_64 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_63);
return x_64;
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
obj* x_6; obj* x_7; uint32 x_10; obj* x_11; obj* x_14; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_6);
lean::dec(x_0);
x_10 = 95;
lean::inc(x_2);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_19 = x_14;
}
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_1);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_15);
lean::cnstr_set(x_23, 2, x_20);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_11 = x_24;
goto lbl_12;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_28 = x_14;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
x_11 = x_30;
goto lbl_12;
}
lbl_12:
{
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
return x_11;
}
else
{
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; uint8 x_39; 
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_42; obj* x_43; obj* x_47; 
lean::dec(x_11);
x_42 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_43 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_42);
x_47 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_42, x_43, x_2);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 2);
lean::inc(x_50);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 x_52 = x_47;
}
x_53 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_48);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_61; 
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_53, 2);
lean::inc(x_58);
lean::dec(x_53);
x_61 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_10, x_56);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_67; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_54, x_62);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_67, 2);
lean::inc(x_72);
lean::dec(x_67);
x_75 = l_lean_string_demangle(x_68);
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_76);
if (lean::is_scalar(x_52)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_52;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_84; 
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 2);
lean::inc(x_84);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_87 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_82);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_88);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_89);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_95; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_95 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_91);
return x_95;
}
else
{
obj* x_96; uint8 x_98; 
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
x_37 = x_91;
x_38 = x_96;
x_39 = x_98;
goto lbl_40;
}
}
else
{
obj* x_99; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_99 = lean::cnstr_get(x_80, 0);
lean::inc(x_99);
lean::dec(x_80);
lean::inc(x_1);
x_103 = lean_name_mk_string(x_1, x_99);
lean::inc(x_7);
x_105 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_103, x_82);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_113; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_113 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_109);
return x_113;
}
else
{
obj* x_114; uint8 x_116; 
x_114 = lean::cnstr_get(x_109, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
x_37 = x_109;
x_38 = x_114;
x_39 = x_116;
goto lbl_40;
}
}
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_117 = lean::cnstr_get(x_79, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_120 = x_79;
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = x_121;
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_122);
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_123);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_129 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_125);
return x_129;
}
else
{
obj* x_130; uint8 x_132; 
x_130 = lean::cnstr_get(x_125, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*1);
x_37 = x_125;
x_38 = x_130;
x_39 = x_132;
goto lbl_40;
}
}
}
else
{
obj* x_134; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_52);
x_134 = lean::cnstr_get(x_67, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_137 = x_67;
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_134);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_136);
x_139 = x_138;
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_139);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_140);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_146; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_146 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_142);
return x_146;
}
else
{
obj* x_147; uint8 x_149; 
x_147 = lean::cnstr_get(x_142, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get_scalar<uint8>(x_142, sizeof(void*)*1);
x_37 = x_142;
x_38 = x_147;
x_39 = x_149;
goto lbl_40;
}
}
}
else
{
obj* x_152; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_52);
lean::dec(x_54);
x_152 = lean::cnstr_get(x_61, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_155 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 x_155 = x_61;
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_152);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = x_156;
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_157);
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_158);
if (lean::obj_tag(x_159) == 0)
{
obj* x_163; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_163 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_159);
return x_163;
}
else
{
obj* x_164; uint8 x_166; 
x_164 = lean::cnstr_get(x_159, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get_scalar<uint8>(x_159, sizeof(void*)*1);
x_37 = x_159;
x_38 = x_164;
x_39 = x_166;
goto lbl_40;
}
}
}
else
{
obj* x_168; uint8 x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
lean::dec(x_52);
x_168 = lean::cnstr_get(x_53, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_171 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_171 = x_53;
}
if (lean::is_scalar(x_171)) {
 x_172 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_172 = x_171;
}
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set_scalar(x_172, sizeof(void*)*1, x_170);
x_173 = x_172;
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_173);
if (lean::obj_tag(x_174) == 0)
{
obj* x_178; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_178 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_174);
return x_178;
}
else
{
obj* x_179; uint8 x_181; 
x_179 = lean::cnstr_get(x_174, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
x_37 = x_174;
x_38 = x_179;
x_39 = x_181;
goto lbl_40;
}
}
}
else
{
obj* x_182; uint8 x_184; obj* x_185; obj* x_187; obj* x_188; 
x_182 = lean::cnstr_get(x_47, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_185 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_185 = x_47;
}
lean::inc(x_182);
if (lean::is_scalar(x_185)) {
 x_187 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_187 = x_185;
}
lean::cnstr_set(x_187, 0, x_182);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_184);
x_188 = x_187;
x_37 = x_188;
x_38 = x_182;
x_39 = x_184;
goto lbl_40;
}
}
else
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_34);
return x_11;
}
lbl_40:
{
if (x_39 == 0)
{
obj* x_194; 
lean::dec(x_37);
x_194 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_10, x_2);
if (lean::obj_tag(x_194) == 0)
{
obj* x_195; obj* x_197; obj* x_200; 
x_195 = lean::cnstr_get(x_194, 1);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 2);
lean::inc(x_197);
lean::dec(x_194);
x_200 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_195);
if (lean::obj_tag(x_200) == 0)
{
obj* x_201; obj* x_203; obj* x_205; obj* x_208; 
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_200, 1);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_200, 2);
lean::inc(x_205);
lean::dec(x_200);
x_208 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_10, x_203);
if (lean::obj_tag(x_208) == 0)
{
obj* x_209; obj* x_211; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_209 = lean::cnstr_get(x_208, 1);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 2);
lean::inc(x_211);
lean::dec(x_208);
x_214 = lean_name_mk_numeral(x_1, x_201);
x_215 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_214, x_209);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_211, x_215);
x_217 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_205, x_216);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_217);
x_219 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_218);
x_220 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_219);
return x_220;
}
else
{
obj* x_224; uint8 x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_201);
x_224 = lean::cnstr_get(x_208, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get_scalar<uint8>(x_208, sizeof(void*)*1);
if (lean::is_shared(x_208)) {
 lean::dec(x_208);
 x_227 = lean::box(0);
} else {
 lean::cnstr_release(x_208, 0);
 x_227 = x_208;
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_224);
lean::cnstr_set_scalar(x_228, sizeof(void*)*1, x_226);
x_229 = x_228;
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_205, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_231);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_232);
return x_233;
}
}
else
{
obj* x_236; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_7);
lean::dec(x_1);
x_236 = lean::cnstr_get(x_200, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_200, sizeof(void*)*1);
if (lean::is_shared(x_200)) {
 lean::dec(x_200);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_200, 0);
 x_239 = x_200;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_236);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_238);
x_241 = x_240;
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_241);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_242);
x_244 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_243);
return x_244;
}
}
else
{
obj* x_247; uint8 x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_7);
lean::dec(x_1);
x_247 = lean::cnstr_get(x_194, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_shared(x_194)) {
 lean::dec(x_194);
 x_250 = lean::box(0);
} else {
 lean::cnstr_release(x_194, 0);
 x_250 = x_194;
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_247);
lean::cnstr_set_scalar(x_251, sizeof(void*)*1, x_249);
x_252 = x_251;
x_253 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_252);
x_254 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_253);
return x_254;
}
}
else
{
obj* x_259; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_259 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_37);
return x_259;
}
}
}
}
}
else
{
obj* x_261; obj* x_263; 
lean::dec(x_0);
x_261 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_261);
x_263 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_263, 0, x_1);
lean::cnstr_set(x_263, 1, x_2);
lean::cnstr_set(x_263, 2, x_261);
return x_263;
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
