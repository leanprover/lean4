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
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_8; obj* x_9; uint8 x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
x_8 = lean::string_iterator_curr(x_1);
x_11 = l_char_is__alpha(x_8);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = l_char_is__digit(x_8);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 95;
x_14 = x_8 == x_13;
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean::box(0);
x_9 = x_15;
goto lbl_10;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::string_iterator_next(x_1);
x_17 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_18 = lean::string_append(x_2, x_17);
x_0 = x_6;
x_1 = x_16;
x_2 = x_18;
goto _start;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::string_iterator_next(x_1);
x_21 = lean::string_push(x_2, x_8);
x_0 = x_6;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
else
{
if (x_11 == 0)
{
uint32 x_23; uint8 x_24; 
x_23 = 95;
x_24 = x_8 == x_23;
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::box(0);
x_9 = x_25;
goto lbl_10;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::string_iterator_next(x_1);
x_27 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_28 = lean::string_append(x_2, x_27);
x_0 = x_6;
x_1 = x_26;
x_2 = x_28;
goto _start;
}
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::string_iterator_next(x_1);
x_31 = lean::string_push(x_2, x_8);
x_0 = x_6;
x_1 = x_30;
x_2 = x_31;
goto _start;
}
}
lbl_10:
{
obj* x_34; obj* x_35; uint8 x_36; 
lean::dec(x_9);
x_34 = lean::uint32_to_nat(x_8);
x_35 = lean::mk_nat_obj(255u);
x_36 = lean::nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint32 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; uint32 x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; uint32 x_53; obj* x_54; obj* x_55; uint32 x_57; obj* x_58; obj* x_59; 
x_37 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_38 = lean::string_append(x_2, x_37);
x_39 = lean::mk_nat_obj(4096u);
x_40 = lean::nat_div(x_34, x_39);
x_41 = l_nat_digit__char(x_40);
x_42 = lean::string_push(x_38, x_41);
x_43 = lean::nat_mod(x_34, x_39);
lean::dec(x_34);
x_45 = lean::mk_nat_obj(256u);
x_46 = lean::nat_div(x_43, x_45);
x_47 = l_nat_digit__char(x_46);
x_48 = lean::string_push(x_42, x_47);
x_49 = lean::nat_mod(x_43, x_45);
lean::dec(x_43);
x_51 = lean::mk_nat_obj(16u);
x_52 = lean::nat_div(x_49, x_51);
x_53 = l_nat_digit__char(x_52);
x_54 = lean::string_push(x_48, x_53);
x_55 = lean::nat_mod(x_49, x_51);
lean::dec(x_49);
x_57 = l_nat_digit__char(x_55);
x_58 = lean::string_push(x_54, x_57);
x_59 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_59;
x_2 = x_58;
goto _start;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint32 x_65; obj* x_66; obj* x_67; uint32 x_69; obj* x_70; obj* x_71; 
x_61 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_62 = lean::string_append(x_2, x_61);
x_63 = lean::mk_nat_obj(16u);
x_64 = lean::nat_div(x_34, x_63);
x_65 = l_nat_digit__char(x_64);
x_66 = lean::string_push(x_62, x_65);
x_67 = lean::nat_mod(x_34, x_63);
lean::dec(x_34);
x_69 = l_nat_digit__char(x_67);
x_70 = lean::string_push(x_66, x_69);
x_71 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_71;
x_2 = x_70;
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
obj* x_102; obj* x_104; obj* x_106; obj* x_108; uint32 x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_119; obj* x_120; 
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
lean::inc(x_99);
if (lean::is_scalar(x_108)) {
 x_119 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_119 = x_108;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_104);
lean::cnstr_set(x_119, 2, x_99);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_106, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_122; obj* x_123; obj* x_125; 
lean::dec(x_0);
x_122 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_120);
x_123 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_123);
x_125 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_122, x_123);
return x_125;
}
else
{
obj* x_126; uint8 x_128; 
x_126 = lean::cnstr_get(x_120, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
x_38 = x_120;
x_39 = x_126;
x_40 = x_128;
goto lbl_41;
}
}
else
{
obj* x_129; uint8 x_131; obj* x_132; obj* x_134; obj* x_135; 
x_129 = lean::cnstr_get(x_101, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_shared(x_101)) {
 lean::dec(x_101);
 x_132 = lean::box(0);
} else {
 lean::cnstr_release(x_101, 0);
 x_132 = x_101;
}
lean::inc(x_129);
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_129);
lean::cnstr_set_scalar(x_134, sizeof(void*)*1, x_131);
x_135 = x_134;
x_38 = x_135;
x_39 = x_129;
x_40 = x_131;
goto lbl_41;
}
}
}
else
{
obj* x_138; obj* x_140; 
lean::dec(x_0);
lean::dec(x_2);
x_138 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_138);
x_140 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_138);
return x_140;
}
lbl_41:
{
if (x_40 == 0)
{
obj* x_142; uint8 x_144; 
lean::dec(x_38);
x_144 = lean::string_iterator_has_next(x_0);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_150; 
x_145 = lean::box(0);
x_146 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_147 = l_mjoin___rarg___closed__1;
lean::inc(x_147);
lean::inc(x_146);
x_150 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_146, x_147, x_145, x_145, x_0);
x_142 = x_150;
goto lbl_143;
}
else
{
uint32 x_151; uint32 x_152; uint8 x_153; uint8 x_155; 
x_151 = lean::string_iterator_curr(x_0);
x_152 = 65;
x_155 = x_152 <= x_151;
if (x_155 == 0)
{
obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_165; 
x_156 = l_char_quote__core(x_151);
x_157 = l_char_has__repr___closed__1;
lean::inc(x_157);
x_159 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_161 = lean::string_append(x_159, x_157);
x_162 = lean::box(0);
x_163 = l_mjoin___rarg___closed__1;
lean::inc(x_163);
x_165 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_161, x_163, x_162, x_162, x_0);
x_142 = x_165;
goto lbl_143;
}
else
{
uint8 x_166; 
x_166 = 1;
x_153 = x_166;
goto lbl_154;
}
lbl_154:
{
uint32 x_167; uint8 x_168; 
x_167 = 70;
x_168 = x_151 <= x_167;
if (x_168 == 0)
{
obj* x_169; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_176; obj* x_178; 
x_169 = l_char_quote__core(x_151);
x_170 = l_char_has__repr___closed__1;
lean::inc(x_170);
x_172 = lean::string_append(x_170, x_169);
lean::dec(x_169);
x_174 = lean::string_append(x_172, x_170);
x_175 = lean::box(0);
x_176 = l_mjoin___rarg___closed__1;
lean::inc(x_176);
x_178 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_174, x_176, x_175, x_175, x_0);
x_142 = x_178;
goto lbl_143;
}
else
{
if (x_153 == 0)
{
obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_186; obj* x_188; 
x_179 = l_char_quote__core(x_151);
x_180 = l_char_has__repr___closed__1;
lean::inc(x_180);
x_182 = lean::string_append(x_180, x_179);
lean::dec(x_179);
x_184 = lean::string_append(x_182, x_180);
x_185 = lean::box(0);
x_186 = l_mjoin___rarg___closed__1;
lean::inc(x_186);
x_188 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_184, x_186, x_185, x_185, x_0);
x_142 = x_188;
goto lbl_143;
}
else
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_189 = lean::string_iterator_next(x_0);
x_190 = lean::box(0);
x_191 = lean::box_uint32(x_151);
x_192 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_189);
lean::cnstr_set(x_192, 2, x_190);
x_142 = x_192;
goto lbl_143;
}
}
}
}
lbl_143:
{
obj* x_193; obj* x_195; 
x_193 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_193);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_142);
if (lean::obj_tag(x_195) == 0)
{
obj* x_196; obj* x_198; obj* x_200; obj* x_202; uint32 x_203; obj* x_205; obj* x_206; obj* x_207; obj* x_209; obj* x_210; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_219; 
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_195, 2);
lean::inc(x_200);
if (lean::is_shared(x_195)) {
 lean::dec(x_195);
 x_202 = lean::box(0);
} else {
 lean::cnstr_release(x_195, 0);
 lean::cnstr_release(x_195, 1);
 lean::cnstr_release(x_195, 2);
 x_202 = x_195;
}
x_203 = lean::unbox_uint32(x_196);
lean::dec(x_196);
x_205 = lean::uint32_to_nat(x_203);
x_206 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_207 = lean::nat_sub(x_205, x_206);
lean::dec(x_205);
x_209 = lean::mk_nat_obj(10u);
x_210 = lean::nat_add(x_209, x_207);
lean::dec(x_207);
lean::inc(x_193);
if (lean::is_scalar(x_202)) {
 x_213 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_213 = x_202;
}
lean::cnstr_set(x_213, 0, x_210);
lean::cnstr_set(x_213, 1, x_198);
lean::cnstr_set(x_213, 2, x_193);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_213);
x_215 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_214);
x_216 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_215);
x_217 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_217);
x_219 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_216, x_217);
return x_219;
}
else
{
obj* x_220; uint8 x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_230; 
x_220 = lean::cnstr_get(x_195, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_shared(x_195)) {
 lean::dec(x_195);
 x_223 = lean::box(0);
} else {
 lean::cnstr_release(x_195, 0);
 x_223 = x_195;
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_220);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_222);
x_225 = x_224;
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_225);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_226);
x_228 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_228);
x_230 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_227, x_228);
return x_230;
}
}
}
else
{
obj* x_233; obj* x_234; obj* x_236; 
lean::dec(x_39);
lean::dec(x_0);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_38);
x_234 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_234);
x_236 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_233, x_234);
return x_236;
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
lean::dec(x_1);
if (x_3 == 0)
{
uint32 x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; 
x_5 = lean::string_iterator_curr(x_0);
x_6 = l_char_quote__core(x_5);
x_7 = l_char_has__repr___closed__1;
lean::inc(x_7);
x_9 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_11 = lean::string_append(x_9, x_7);
x_12 = lean::box(0);
x_13 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
lean::inc(x_13);
x_15 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_11, x_13, x_12, x_12, x_0);
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_22; 
x_19 = lean::box(0);
x_20 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_20);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_0);
lean::cnstr_set(x_22, 2, x_20);
return x_22;
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
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
lean::inc(x_2);
x_11 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_17);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_20);
x_8 = x_21;
goto lbl_9;
}
else
{
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_25 = x_11;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_24);
x_27 = x_26;
x_8 = x_27;
goto lbl_9;
}
lbl_9:
{
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_8;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_31 = lean::cnstr_get(x_8, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_33 == 0)
{
obj* x_40; 
lean::dec(x_8);
lean::inc(x_2);
x_40 = l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_45; uint32 x_48; obj* x_51; obj* x_53; obj* x_54; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 2);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::unbox_uint32(x_41);
lean::dec(x_41);
lean::inc(x_1);
x_51 = lean::string_push(x_1, x_48);
lean::inc(x_6);
x_53 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_51, x_43);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_58; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_58 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_54);
return x_58;
}
else
{
obj* x_59; uint8 x_61; 
x_59 = lean::cnstr_get(x_54, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
x_34 = x_54;
x_35 = x_59;
x_36 = x_61;
goto lbl_37;
}
}
else
{
obj* x_62; uint8 x_64; obj* x_65; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_40, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 x_65 = x_40;
}
lean::inc(x_62);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_64);
x_68 = x_67;
x_34 = x_68;
x_35 = x_62;
x_36 = x_64;
goto lbl_37;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_31);
return x_8;
}
lbl_37:
{
obj* x_73; obj* x_74; uint8 x_75; 
if (x_36 == 0)
{
obj* x_79; 
lean::dec(x_34);
lean::inc(x_2);
x_79 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_84; uint32 x_87; obj* x_90; obj* x_92; obj* x_93; 
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_79, 2);
lean::inc(x_84);
lean::dec(x_79);
x_87 = lean::unbox_uint32(x_80);
lean::dec(x_80);
lean::inc(x_1);
x_90 = lean::string_push(x_1, x_87);
lean::inc(x_6);
x_92 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_90, x_82);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_98; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_97 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_93);
x_98 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_97);
return x_98;
}
else
{
obj* x_99; uint8 x_101; 
x_99 = lean::cnstr_get(x_93, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<uint8>(x_93, sizeof(void*)*1);
x_73 = x_93;
x_74 = x_99;
x_75 = x_101;
goto lbl_76;
}
}
else
{
obj* x_102; uint8 x_104; obj* x_105; obj* x_107; obj* x_108; 
x_102 = lean::cnstr_get(x_79, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_105 = x_79;
}
lean::inc(x_102);
if (lean::is_scalar(x_105)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_105;
}
lean::cnstr_set(x_107, 0, x_102);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_104);
x_108 = x_107;
x_73 = x_108;
x_74 = x_102;
x_75 = x_104;
goto lbl_76;
}
}
else
{
obj* x_113; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_35);
x_113 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_34);
return x_113;
}
lbl_76:
{
obj* x_114; obj* x_115; uint8 x_116; 
if (x_75 == 0)
{
obj* x_119; obj* x_120; obj* x_124; 
lean::dec(x_73);
x_119 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_120 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
lean::inc(x_120);
lean::inc(x_119);
x_124 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_119, x_120, x_2);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_127; uint32 x_130; obj* x_132; obj* x_134; obj* x_135; 
x_125 = lean::cnstr_get(x_124, 1);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 2);
lean::inc(x_127);
lean::dec(x_124);
x_130 = 95;
lean::inc(x_1);
x_132 = lean::string_push(x_1, x_130);
lean::inc(x_6);
x_134 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_132, x_125);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_127, x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_139 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_135);
x_140 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_139);
x_141 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_140);
return x_141;
}
else
{
obj* x_142; uint8 x_144; 
x_142 = lean::cnstr_get(x_135, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get_scalar<uint8>(x_135, sizeof(void*)*1);
x_114 = x_135;
x_115 = x_142;
x_116 = x_144;
goto lbl_117;
}
}
else
{
obj* x_145; uint8 x_147; obj* x_148; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_124, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*1);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_148 = x_124;
}
lean::inc(x_145);
if (lean::is_scalar(x_148)) {
 x_150 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_150 = x_148;
}
lean::cnstr_set(x_150, 0, x_145);
lean::cnstr_set_scalar(x_150, sizeof(void*)*1, x_147);
x_151 = x_150;
x_114 = x_151;
x_115 = x_145;
x_116 = x_147;
goto lbl_117;
}
}
else
{
obj* x_156; obj* x_157; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_74);
x_156 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_73);
x_157 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_156);
return x_157;
}
lbl_117:
{
obj* x_158; obj* x_159; uint8 x_160; 
if (x_116 == 0)
{
obj* x_163; obj* x_164; obj* x_168; 
lean::dec(x_114);
x_163 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_164 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_164);
lean::inc(x_163);
x_168 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_163, x_164, x_2);
if (lean::obj_tag(x_168) == 0)
{
obj* x_169; obj* x_171; obj* x_174; 
x_169 = lean::cnstr_get(x_168, 1);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 2);
lean::inc(x_171);
lean::dec(x_168);
x_174 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_169);
if (lean::obj_tag(x_174) == 0)
{
obj* x_175; obj* x_177; obj* x_179; obj* x_182; 
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 1);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_174, 2);
lean::inc(x_179);
lean::dec(x_174);
x_182 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_177);
if (lean::obj_tag(x_182) == 0)
{
obj* x_183; obj* x_185; obj* x_187; obj* x_190; obj* x_191; obj* x_193; uint32 x_196; obj* x_198; obj* x_200; obj* x_201; obj* x_202; obj* x_203; 
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_182, 1);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_182, 2);
lean::inc(x_187);
lean::dec(x_182);
x_190 = lean::mk_nat_obj(16u);
x_191 = lean::nat_mul(x_175, x_190);
lean::dec(x_175);
x_193 = lean::nat_add(x_191, x_183);
lean::dec(x_183);
lean::dec(x_191);
x_196 = l_char_of__nat(x_193);
lean::inc(x_1);
x_198 = lean::string_push(x_1, x_196);
lean::inc(x_6);
x_200 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_198, x_185);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_187, x_200);
x_202 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_179, x_201);
x_203 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_202);
if (lean::obj_tag(x_203) == 0)
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_207 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_203);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_207);
x_209 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_208);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_209);
return x_210;
}
else
{
obj* x_211; uint8 x_213; 
x_211 = lean::cnstr_get(x_203, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get_scalar<uint8>(x_203, sizeof(void*)*1);
x_158 = x_203;
x_159 = x_211;
x_160 = x_213;
goto lbl_161;
}
}
else
{
obj* x_215; uint8 x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_175);
x_215 = lean::cnstr_get(x_182, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get_scalar<uint8>(x_182, sizeof(void*)*1);
if (lean::is_shared(x_182)) {
 lean::dec(x_182);
 x_218 = lean::box(0);
} else {
 lean::cnstr_release(x_182, 0);
 x_218 = x_182;
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_215);
lean::cnstr_set_scalar(x_219, sizeof(void*)*1, x_217);
x_220 = x_219;
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_179, x_220);
x_222 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_221);
if (lean::obj_tag(x_222) == 0)
{
obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_222);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_226);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_227);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_228);
return x_229;
}
else
{
obj* x_230; uint8 x_232; 
x_230 = lean::cnstr_get(x_222, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get_scalar<uint8>(x_222, sizeof(void*)*1);
x_158 = x_222;
x_159 = x_230;
x_160 = x_232;
goto lbl_161;
}
}
}
else
{
obj* x_233; uint8 x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_233 = lean::cnstr_get(x_174, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
if (lean::is_shared(x_174)) {
 lean::dec(x_174);
 x_236 = lean::box(0);
} else {
 lean::cnstr_release(x_174, 0);
 x_236 = x_174;
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_233);
lean::cnstr_set_scalar(x_237, sizeof(void*)*1, x_235);
x_238 = x_237;
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_239);
x_244 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_243);
x_245 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_244);
x_246 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_245);
return x_246;
}
else
{
obj* x_247; uint8 x_249; 
x_247 = lean::cnstr_get(x_239, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get_scalar<uint8>(x_239, sizeof(void*)*1);
x_158 = x_239;
x_159 = x_247;
x_160 = x_249;
goto lbl_161;
}
}
}
else
{
obj* x_250; uint8 x_252; obj* x_253; obj* x_255; obj* x_256; 
x_250 = lean::cnstr_get(x_168, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_shared(x_168)) {
 lean::dec(x_168);
 x_253 = lean::box(0);
} else {
 lean::cnstr_release(x_168, 0);
 x_253 = x_168;
}
lean::inc(x_250);
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_250);
lean::cnstr_set_scalar(x_255, sizeof(void*)*1, x_252);
x_256 = x_255;
x_158 = x_256;
x_159 = x_250;
x_160 = x_252;
goto lbl_161;
}
}
else
{
obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_115);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_261 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_114);
x_262 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_261);
x_263 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_262);
return x_263;
}
lbl_161:
{
if (x_160 == 0)
{
obj* x_265; obj* x_266; obj* x_269; 
lean::dec(x_158);
x_265 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_266 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
lean::inc(x_266);
lean::inc(x_265);
x_269 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_265, x_266, x_2);
if (lean::obj_tag(x_269) == 0)
{
obj* x_270; obj* x_272; obj* x_275; 
x_270 = lean::cnstr_get(x_269, 1);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_269, 2);
lean::inc(x_272);
lean::dec(x_269);
x_275 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_270);
if (lean::obj_tag(x_275) == 0)
{
obj* x_276; obj* x_278; obj* x_280; obj* x_283; 
x_276 = lean::cnstr_get(x_275, 0);
lean::inc(x_276);
x_278 = lean::cnstr_get(x_275, 1);
lean::inc(x_278);
x_280 = lean::cnstr_get(x_275, 2);
lean::inc(x_280);
lean::dec(x_275);
x_283 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_278);
if (lean::obj_tag(x_283) == 0)
{
obj* x_284; obj* x_286; obj* x_288; obj* x_291; 
x_284 = lean::cnstr_get(x_283, 0);
lean::inc(x_284);
x_286 = lean::cnstr_get(x_283, 1);
lean::inc(x_286);
x_288 = lean::cnstr_get(x_283, 2);
lean::inc(x_288);
lean::dec(x_283);
x_291 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_286);
if (lean::obj_tag(x_291) == 0)
{
obj* x_292; obj* x_294; obj* x_296; obj* x_299; 
x_292 = lean::cnstr_get(x_291, 0);
lean::inc(x_292);
x_294 = lean::cnstr_get(x_291, 1);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_291, 2);
lean::inc(x_296);
lean::dec(x_291);
x_299 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_294);
if (lean::obj_tag(x_299) == 0)
{
obj* x_300; obj* x_302; obj* x_304; obj* x_307; obj* x_308; obj* x_310; obj* x_311; obj* x_313; obj* x_316; obj* x_317; obj* x_319; obj* x_322; uint32 x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; 
x_300 = lean::cnstr_get(x_299, 0);
lean::inc(x_300);
x_302 = lean::cnstr_get(x_299, 1);
lean::inc(x_302);
x_304 = lean::cnstr_get(x_299, 2);
lean::inc(x_304);
lean::dec(x_299);
x_307 = lean::mk_nat_obj(4096u);
x_308 = lean::nat_mul(x_276, x_307);
lean::dec(x_276);
x_310 = lean::mk_nat_obj(256u);
x_311 = lean::nat_mul(x_284, x_310);
lean::dec(x_284);
x_313 = lean::nat_add(x_308, x_311);
lean::dec(x_311);
lean::dec(x_308);
x_316 = lean::mk_nat_obj(16u);
x_317 = lean::nat_mul(x_292, x_316);
lean::dec(x_292);
x_319 = lean::nat_add(x_313, x_317);
lean::dec(x_317);
lean::dec(x_313);
x_322 = lean::nat_add(x_319, x_300);
lean::dec(x_300);
lean::dec(x_319);
x_325 = l_char_of__nat(x_322);
x_326 = lean::string_push(x_1, x_325);
x_327 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_326, x_302);
x_328 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_304, x_327);
x_329 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_296, x_328);
x_330 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_329);
x_331 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_330);
x_332 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_331);
x_333 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_332);
x_334 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_333);
x_335 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_334);
x_336 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_335);
x_337 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_336);
return x_337;
}
else
{
obj* x_343; uint8 x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_292);
lean::dec(x_284);
lean::dec(x_276);
x_343 = lean::cnstr_get(x_299, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get_scalar<uint8>(x_299, sizeof(void*)*1);
if (lean::is_shared(x_299)) {
 lean::dec(x_299);
 x_346 = lean::box(0);
} else {
 lean::cnstr_release(x_299, 0);
 x_346 = x_299;
}
if (lean::is_scalar(x_346)) {
 x_347 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_347 = x_346;
}
lean::cnstr_set(x_347, 0, x_343);
lean::cnstr_set_scalar(x_347, sizeof(void*)*1, x_345);
x_348 = x_347;
x_349 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_296, x_348);
x_350 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_349);
x_351 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_350);
x_352 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_351);
x_353 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_352);
x_354 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_353);
x_355 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_354);
x_356 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_355);
x_357 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_356);
return x_357;
}
}
else
{
obj* x_362; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_284);
lean::dec(x_276);
x_362 = lean::cnstr_get(x_291, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get_scalar<uint8>(x_291, sizeof(void*)*1);
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_365 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_365 = x_291;
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set_scalar(x_366, sizeof(void*)*1, x_364);
x_367 = x_366;
x_368 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_367);
x_369 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_368);
x_370 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_369);
x_371 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_370);
x_372 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_371);
x_373 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_372);
x_374 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_373);
x_375 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_374);
return x_375;
}
}
else
{
obj* x_379; uint8 x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_276);
x_379 = lean::cnstr_get(x_283, 0);
lean::inc(x_379);
x_381 = lean::cnstr_get_scalar<uint8>(x_283, sizeof(void*)*1);
if (lean::is_shared(x_283)) {
 lean::dec(x_283);
 x_382 = lean::box(0);
} else {
 lean::cnstr_release(x_283, 0);
 x_382 = x_283;
}
if (lean::is_scalar(x_382)) {
 x_383 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_383 = x_382;
}
lean::cnstr_set(x_383, 0, x_379);
lean::cnstr_set_scalar(x_383, sizeof(void*)*1, x_381);
x_384 = x_383;
x_385 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_384);
x_386 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_385);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_386);
x_388 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_387);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_388);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_389);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_390);
return x_391;
}
}
else
{
obj* x_394; uint8 x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; 
lean::dec(x_6);
lean::dec(x_1);
x_394 = lean::cnstr_get(x_275, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get_scalar<uint8>(x_275, sizeof(void*)*1);
if (lean::is_shared(x_275)) {
 lean::dec(x_275);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_275, 0);
 x_397 = x_275;
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_394);
lean::cnstr_set_scalar(x_398, sizeof(void*)*1, x_396);
x_399 = x_398;
x_400 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_399);
x_401 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_400);
x_402 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_401);
x_403 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_402);
x_404 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_403);
x_405 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_404);
return x_405;
}
}
else
{
obj* x_408; uint8 x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; 
lean::dec(x_6);
lean::dec(x_1);
x_408 = lean::cnstr_get(x_269, 0);
lean::inc(x_408);
x_410 = lean::cnstr_get_scalar<uint8>(x_269, sizeof(void*)*1);
if (lean::is_shared(x_269)) {
 lean::dec(x_269);
 x_411 = lean::box(0);
} else {
 lean::cnstr_release(x_269, 0);
 x_411 = x_269;
}
if (lean::is_scalar(x_411)) {
 x_412 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_412 = x_411;
}
lean::cnstr_set(x_412, 0, x_408);
lean::cnstr_set_scalar(x_412, sizeof(void*)*1, x_410);
x_413 = x_412;
x_414 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_413);
x_415 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_414);
x_416 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_415);
x_417 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_416);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_417);
return x_418;
}
}
else
{
obj* x_423; obj* x_424; obj* x_425; obj* x_426; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_159);
x_423 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_115, x_158);
x_424 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_423);
x_425 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_424);
x_426 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_425);
return x_426;
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
obj* x_428; obj* x_430; 
lean::dec(x_0);
x_428 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_428);
x_430 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_430, 0, x_1);
lean::cnstr_set(x_430, 1, x_2);
lean::cnstr_set(x_430, 2, x_428);
return x_430;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
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
if (x_3 == 0)
{
obj* x_4; obj* x_6; 
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = l___private_init_lean_parser_parsec_2__take__aux___main___rarg(x_0, x_4, x_1);
return x_6;
}
else
{
obj* x_8; obj* x_9; obj* x_12; 
lean::dec(x_0);
x_8 = l_string_join___closed__1;
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_9);
return x_12;
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
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_8; obj* x_9; obj* x_12; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
x_8 = 95;
lean::inc(x_2);
x_12 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
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
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
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
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; uint8 x_37; 
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_34 == 0)
{
obj* x_40; obj* x_41; obj* x_45; 
lean::dec(x_9);
x_40 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_41 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_40);
x_45 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_40, x_41, x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 lean::cnstr_release(x_45, 2);
 x_50 = x_45;
}
x_51 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_46);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_54; obj* x_56; obj* x_59; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 2);
lean::inc(x_56);
lean::dec(x_51);
x_59 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_54);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_62; obj* x_65; 
x_60 = lean::cnstr_get(x_59, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 2);
lean::inc(x_62);
lean::dec(x_59);
x_65 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_52, x_60);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_77; 
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_65, 2);
lean::inc(x_70);
lean::dec(x_65);
x_73 = l_lean_string_demangle(x_66);
x_74 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_74);
if (lean::is_scalar(x_50)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_50;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_68);
lean::cnstr_set(x_76, 2, x_74);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_85 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_80);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_85);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_86);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_93 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_89);
return x_93;
}
else
{
obj* x_94; uint8 x_96; 
x_94 = lean::cnstr_get(x_89, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
x_35 = x_89;
x_36 = x_94;
x_37 = x_96;
goto lbl_38;
}
}
else
{
obj* x_97; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_97 = lean::cnstr_get(x_78, 0);
lean::inc(x_97);
lean::dec(x_78);
lean::inc(x_1);
x_101 = lean_name_mk_string(x_1, x_97);
lean::inc(x_6);
x_103 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_101, x_80);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_103);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_104);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_106);
if (lean::obj_tag(x_107) == 0)
{
obj* x_111; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_111 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_107);
return x_111;
}
else
{
obj* x_112; uint8 x_114; 
x_112 = lean::cnstr_get(x_107, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get_scalar<uint8>(x_107, sizeof(void*)*1);
x_35 = x_107;
x_36 = x_112;
x_37 = x_114;
goto lbl_38;
}
}
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_77, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_118 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_118 = x_77;
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_121);
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_127; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_127 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_123);
return x_127;
}
else
{
obj* x_128; uint8 x_130; 
x_128 = lean::cnstr_get(x_123, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*1);
x_35 = x_123;
x_36 = x_128;
x_37 = x_130;
goto lbl_38;
}
}
}
else
{
obj* x_132; uint8 x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_50);
x_132 = lean::cnstr_get(x_65, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get_scalar<uint8>(x_65, sizeof(void*)*1);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_135 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 x_135 = x_65;
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_132);
lean::cnstr_set_scalar(x_136, sizeof(void*)*1, x_134);
x_137 = x_136;
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_137);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_144; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_144 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_140);
return x_144;
}
else
{
obj* x_145; uint8 x_147; 
x_145 = lean::cnstr_get(x_140, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
x_35 = x_140;
x_36 = x_145;
x_37 = x_147;
goto lbl_38;
}
}
}
else
{
obj* x_150; uint8 x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_50);
lean::dec(x_52);
x_150 = lean::cnstr_get(x_59, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get_scalar<uint8>(x_59, sizeof(void*)*1);
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 x_153 = x_59;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_150);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = x_154;
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_161; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_161 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_157);
return x_161;
}
else
{
obj* x_162; uint8 x_164; 
x_162 = lean::cnstr_get(x_157, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
x_35 = x_157;
x_36 = x_162;
x_37 = x_164;
goto lbl_38;
}
}
}
else
{
obj* x_166; uint8 x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_50);
x_166 = lean::cnstr_get(x_51, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_169 = x_51;
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_168);
x_171 = x_170;
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_171);
if (lean::obj_tag(x_172) == 0)
{
obj* x_176; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_176 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_172);
return x_176;
}
else
{
obj* x_177; uint8 x_179; 
x_177 = lean::cnstr_get(x_172, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get_scalar<uint8>(x_172, sizeof(void*)*1);
x_35 = x_172;
x_36 = x_177;
x_37 = x_179;
goto lbl_38;
}
}
}
else
{
obj* x_180; uint8 x_182; obj* x_183; obj* x_185; obj* x_186; 
x_180 = lean::cnstr_get(x_45, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_183 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 x_183 = x_45;
}
lean::inc(x_180);
if (lean::is_scalar(x_183)) {
 x_185 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_185 = x_183;
}
lean::cnstr_set(x_185, 0, x_180);
lean::cnstr_set_scalar(x_185, sizeof(void*)*1, x_182);
x_186 = x_185;
x_35 = x_186;
x_36 = x_180;
x_37 = x_182;
goto lbl_38;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_32);
return x_9;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_192; 
lean::dec(x_35);
x_192 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_2);
if (lean::obj_tag(x_192) == 0)
{
obj* x_193; obj* x_195; obj* x_198; 
x_193 = lean::cnstr_get(x_192, 1);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 2);
lean::inc(x_195);
lean::dec(x_192);
x_198 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_193);
if (lean::obj_tag(x_198) == 0)
{
obj* x_199; obj* x_201; obj* x_203; obj* x_206; 
x_199 = lean::cnstr_get(x_198, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_198, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_198, 2);
lean::inc(x_203);
lean::dec(x_198);
x_206 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_201);
if (lean::obj_tag(x_206) == 0)
{
obj* x_207; obj* x_209; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; 
x_207 = lean::cnstr_get(x_206, 1);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 2);
lean::inc(x_209);
lean::dec(x_206);
x_212 = lean_name_mk_numeral(x_1, x_199);
x_213 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_212, x_207);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_209, x_213);
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_215);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_216);
x_218 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_217);
return x_218;
}
else
{
obj* x_222; uint8 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_199);
x_222 = lean::cnstr_get(x_206, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get_scalar<uint8>(x_206, sizeof(void*)*1);
if (lean::is_shared(x_206)) {
 lean::dec(x_206);
 x_225 = lean::box(0);
} else {
 lean::cnstr_release(x_206, 0);
 x_225 = x_206;
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set_scalar(x_226, sizeof(void*)*1, x_224);
x_227 = x_226;
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_227);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_228);
x_230 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_229);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_230);
return x_231;
}
}
else
{
obj* x_234; uint8 x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_6);
lean::dec(x_1);
x_234 = lean::cnstr_get(x_198, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get_scalar<uint8>(x_198, sizeof(void*)*1);
if (lean::is_shared(x_198)) {
 lean::dec(x_198);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_198, 0);
 x_237 = x_198;
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_234);
lean::cnstr_set_scalar(x_238, sizeof(void*)*1, x_236);
x_239 = x_238;
x_240 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_239);
x_241 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_240);
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_241);
return x_242;
}
}
else
{
obj* x_245; uint8 x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_6);
lean::dec(x_1);
x_245 = lean::cnstr_get(x_192, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*1);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_248 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 x_248 = x_192;
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_245);
lean::cnstr_set_scalar(x_249, sizeof(void*)*1, x_247);
x_250 = x_249;
x_251 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_250);
x_252 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_251);
return x_252;
}
}
else
{
obj* x_257; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_36);
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_35);
return x_257;
}
}
}
}
}
else
{
obj* x_259; obj* x_261; 
lean::dec(x_0);
x_259 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_259);
x_261 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_261, 0, x_1);
lean::cnstr_set(x_261, 1, x_2);
lean::cnstr_set(x_261, 2, x_259);
return x_261;
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
