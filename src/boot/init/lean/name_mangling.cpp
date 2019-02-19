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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_name__mangling_1__string_mangle__aux___main(x_1, x_2, x_3);
return x_4;
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
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
x_11 = lean::box(0);
x_12 = l_string_join___closed__1;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_1);
lean::cnstr_set(x_13, 3, x_11);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
return x_16;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
x_26 = l_string_join___closed__1;
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_2);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_5);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_0);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = l_char_quote__core(x_8);
x_11 = l_char_has__repr___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_12, x_11);
x_15 = lean::box(0);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_14, x_16, x_15, x_15, x_0);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::string_iterator_next(x_0);
x_21 = lean::box(0);
x_22 = lean::box_uint32(x_8);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_13 = x_6;
} else {
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_16 = lean::uint32_to_nat(x_14);
x_17 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_18 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_9);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_0);
x_24 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_25 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_22, x_24);
return x_25;
}
else
{
obj* x_26; uint8 x_28; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
x_1 = x_22;
x_2 = x_26;
x_3 = x_28;
goto lbl_4;
}
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_6, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_32 = x_6;
} else {
 lean::dec(x_6);
 x_32 = lean::box(0);
}
lean::inc(x_29);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_31);
x_35 = x_34;
x_1 = x_35;
x_2 = x_29;
x_3 = x_31;
goto lbl_4;
}
lbl_4:
{
obj* x_36; obj* x_37; uint8 x_38; 
if (x_3 == 0)
{
obj* x_41; uint8 x_43; 
lean::dec(x_1);
x_43 = lean::string_iterator_has_next(x_0);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_48; 
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_48 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_45, x_46, x_44, x_44, x_0);
x_41 = x_48;
goto lbl_42;
}
else
{
uint32 x_49; uint32 x_50; uint8 x_51; uint8 x_53; 
x_49 = lean::string_iterator_curr(x_0);
x_50 = 97;
x_53 = x_50 <= x_49;
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_62; 
x_54 = l_char_quote__core(x_49);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_62 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_58, x_60, x_59, x_59, x_0);
x_41 = x_62;
goto lbl_42;
}
else
{
uint8 x_63; 
x_63 = 1;
x_51 = x_63;
goto lbl_52;
}
lbl_52:
{
uint32 x_64; uint8 x_65; 
x_64 = 102;
x_65 = x_49 <= x_64;
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; 
x_66 = l_char_quote__core(x_49);
x_67 = l_char_has__repr___closed__1;
x_68 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_70 = lean::string_append(x_68, x_67);
x_71 = lean::box(0);
x_72 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_74 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_70, x_72, x_71, x_71, x_0);
x_41 = x_74;
goto lbl_42;
}
else
{
if (x_51 == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_83; 
x_75 = l_char_quote__core(x_49);
x_76 = l_char_has__repr___closed__1;
x_77 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_79 = lean::string_append(x_77, x_76);
x_80 = lean::box(0);
x_81 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_83 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_79, x_81, x_80, x_80, x_0);
x_41 = x_83;
goto lbl_42;
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::inc(x_0);
x_85 = lean::string_iterator_next(x_0);
x_86 = lean::box(0);
x_87 = lean::box_uint32(x_49);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_85);
lean::cnstr_set(x_88, 2, x_86);
x_41 = x_88;
goto lbl_42;
}
}
}
}
lbl_42:
{
obj* x_89; obj* x_90; 
x_89 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_41);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_93; obj* x_95; obj* x_97; uint32 x_98; obj* x_100; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_108; 
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_90, 2);
lean::inc(x_95);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 lean::cnstr_release(x_90, 2);
 x_97 = x_90;
} else {
 lean::dec(x_90);
 x_97 = lean::box(0);
}
x_98 = lean::unbox_uint32(x_91);
lean::dec(x_91);
x_100 = lean::uint32_to_nat(x_98);
x_101 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_102 = lean::nat_sub(x_100, x_101);
lean::dec(x_100);
x_104 = lean::mk_nat_obj(10u);
x_105 = lean::nat_add(x_104, x_102);
lean::dec(x_102);
if (lean::is_scalar(x_97)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_97;
}
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_93);
lean::cnstr_set(x_107, 2, x_89);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_0);
x_110 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_108);
x_111 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_112 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_110, x_111);
return x_112;
}
else
{
obj* x_113; uint8 x_115; 
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<uint8>(x_108, sizeof(void*)*1);
x_36 = x_108;
x_37 = x_113;
x_38 = x_115;
goto lbl_39;
}
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_121; obj* x_122; 
x_116 = lean::cnstr_get(x_90, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 x_119 = x_90;
} else {
 lean::dec(x_90);
 x_119 = lean::box(0);
}
lean::inc(x_116);
if (lean::is_scalar(x_119)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_119;
}
lean::cnstr_set(x_121, 0, x_116);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_118);
x_122 = x_121;
x_36 = x_122;
x_37 = x_116;
x_38 = x_118;
goto lbl_39;
}
}
}
else
{
obj* x_125; obj* x_126; 
lean::dec(x_0);
lean::dec(x_2);
x_125 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_125);
return x_126;
}
lbl_39:
{
if (x_38 == 0)
{
obj* x_128; uint8 x_130; 
lean::dec(x_36);
x_130 = lean::string_iterator_has_next(x_0);
if (x_130 == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_131 = lean::box(0);
x_132 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_133 = l_mjoin___rarg___closed__1;
x_134 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_132, x_133, x_131, x_131, x_0);
x_128 = x_134;
goto lbl_129;
}
else
{
uint32 x_135; uint32 x_136; uint8 x_137; uint8 x_139; 
x_135 = lean::string_iterator_curr(x_0);
x_136 = 65;
x_139 = x_136 <= x_135;
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_140 = l_char_quote__core(x_135);
x_141 = l_char_has__repr___closed__1;
x_142 = lean::string_append(x_141, x_140);
lean::dec(x_140);
x_144 = lean::string_append(x_142, x_141);
x_145 = lean::box(0);
x_146 = l_mjoin___rarg___closed__1;
x_147 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_144, x_146, x_145, x_145, x_0);
x_128 = x_147;
goto lbl_129;
}
else
{
uint8 x_148; 
x_148 = 1;
x_137 = x_148;
goto lbl_138;
}
lbl_138:
{
uint32 x_149; uint8 x_150; 
x_149 = 70;
x_150 = x_135 <= x_149;
if (x_150 == 0)
{
obj* x_151; obj* x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_151 = l_char_quote__core(x_135);
x_152 = l_char_has__repr___closed__1;
x_153 = lean::string_append(x_152, x_151);
lean::dec(x_151);
x_155 = lean::string_append(x_153, x_152);
x_156 = lean::box(0);
x_157 = l_mjoin___rarg___closed__1;
x_158 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_155, x_157, x_156, x_156, x_0);
x_128 = x_158;
goto lbl_129;
}
else
{
if (x_137 == 0)
{
obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_159 = l_char_quote__core(x_135);
x_160 = l_char_has__repr___closed__1;
x_161 = lean::string_append(x_160, x_159);
lean::dec(x_159);
x_163 = lean::string_append(x_161, x_160);
x_164 = lean::box(0);
x_165 = l_mjoin___rarg___closed__1;
x_166 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_163, x_165, x_164, x_164, x_0);
x_128 = x_166;
goto lbl_129;
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
x_167 = lean::string_iterator_next(x_0);
x_168 = lean::box(0);
x_169 = lean::box_uint32(x_135);
x_170 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_167);
lean::cnstr_set(x_170, 2, x_168);
x_128 = x_170;
goto lbl_129;
}
}
}
}
lbl_129:
{
obj* x_171; obj* x_172; 
x_171 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_128);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_175; obj* x_177; obj* x_179; uint32 x_180; obj* x_182; obj* x_183; obj* x_184; obj* x_186; obj* x_187; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_172, 1);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_172, 2);
lean::inc(x_177);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 lean::cnstr_release(x_172, 2);
 x_179 = x_172;
} else {
 lean::dec(x_172);
 x_179 = lean::box(0);
}
x_180 = lean::unbox_uint32(x_173);
lean::dec(x_173);
x_182 = lean::uint32_to_nat(x_180);
x_183 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_184 = lean::nat_sub(x_182, x_183);
lean::dec(x_182);
x_186 = lean::mk_nat_obj(10u);
x_187 = lean::nat_add(x_186, x_184);
lean::dec(x_184);
if (lean::is_scalar(x_179)) {
 x_189 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_189 = x_179;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_175);
lean::cnstr_set(x_189, 2, x_171);
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_177, x_189);
x_191 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_190);
x_192 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_191);
x_193 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_194 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_192, x_193);
return x_194;
}
else
{
obj* x_195; uint8 x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_195 = lean::cnstr_get(x_172, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get_scalar<uint8>(x_172, sizeof(void*)*1);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 x_198 = x_172;
} else {
 lean::dec(x_172);
 x_198 = lean::box(0);
}
if (lean::is_scalar(x_198)) {
 x_199 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_199 = x_198;
}
lean::cnstr_set(x_199, 0, x_195);
lean::cnstr_set_scalar(x_199, sizeof(void*)*1, x_197);
x_200 = x_199;
x_201 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_200);
x_202 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_201);
x_203 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_204 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_202, x_203);
return x_204;
}
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_37);
lean::dec(x_0);
x_207 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_36);
x_208 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_209 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_207, x_208);
return x_209;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_5);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_0);
x_9 = l_char_is__alpha(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = l_char_quote__core(x_8);
x_11 = l_char_has__repr___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = lean::string_append(x_12, x_11);
x_15 = lean::box(0);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_14, x_16, x_15, x_15, x_0);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::string_iterator_next(x_0);
x_21 = lean::box(0);
x_22 = lean::box_uint32(x_8);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
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
uint32 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::string_iterator_curr(x_0);
x_6 = l_char_quote__core(x_5);
x_7 = l_char_has__repr___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = lean::string_append(x_8, x_7);
x_11 = lean::box(0);
x_12 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
x_13 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_10, x_12, x_11, x_11, x_0);
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::box(0);
x_17 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_0);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
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
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_16 = x_11;
} else {
 lean::dec(x_11);
 x_16 = lean::box(0);
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
x_8 = x_20;
goto lbl_9;
}
else
{
obj* x_21; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_11, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_24 = x_11;
} else {
 lean::dec(x_11);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_23);
x_26 = x_25;
x_8 = x_26;
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
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_30 = lean::cnstr_get(x_8, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_32 == 0)
{
obj* x_39; 
lean::dec(x_8);
lean::inc(x_2);
x_39 = l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_44; uint32 x_47; obj* x_50; obj* x_52; obj* x_53; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 2);
lean::inc(x_44);
lean::dec(x_39);
x_47 = lean::unbox_uint32(x_40);
lean::dec(x_40);
lean::inc(x_1);
x_50 = lean::string_push(x_1, x_47);
lean::inc(x_6);
x_52 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_50, x_42);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_57; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_57 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_53);
return x_57;
}
else
{
obj* x_58; uint8 x_60; 
x_58 = lean::cnstr_get(x_53, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
x_33 = x_53;
x_34 = x_58;
x_35 = x_60;
goto lbl_36;
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_66; obj* x_67; 
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_64 = x_39;
} else {
 lean::dec(x_39);
 x_64 = lean::box(0);
}
lean::inc(x_61);
if (lean::is_scalar(x_64)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_64;
}
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_63);
x_67 = x_66;
x_33 = x_67;
x_34 = x_61;
x_35 = x_63;
goto lbl_36;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_30);
return x_8;
}
lbl_36:
{
obj* x_72; obj* x_73; uint8 x_74; 
if (x_35 == 0)
{
obj* x_78; 
lean::dec(x_33);
lean::inc(x_2);
x_78 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_81; obj* x_83; uint32 x_86; obj* x_89; obj* x_91; obj* x_92; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_86 = lean::unbox_uint32(x_79);
lean::dec(x_79);
lean::inc(x_1);
x_89 = lean::string_push(x_1, x_86);
lean::inc(x_6);
x_91 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_89, x_81);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_96; obj* x_97; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_96 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_92);
x_97 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_96);
return x_97;
}
else
{
obj* x_98; uint8 x_100; 
x_98 = lean::cnstr_get(x_92, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get_scalar<uint8>(x_92, sizeof(void*)*1);
x_72 = x_92;
x_73 = x_98;
x_74 = x_100;
goto lbl_75;
}
}
else
{
obj* x_101; uint8 x_103; obj* x_104; obj* x_106; obj* x_107; 
x_101 = lean::cnstr_get(x_78, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_104 = x_78;
} else {
 lean::dec(x_78);
 x_104 = lean::box(0);
}
lean::inc(x_101);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_101);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_103);
x_107 = x_106;
x_72 = x_107;
x_73 = x_101;
x_74 = x_103;
goto lbl_75;
}
}
else
{
obj* x_112; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_34);
x_112 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_33);
return x_112;
}
lbl_75:
{
obj* x_113; obj* x_114; uint8 x_115; 
if (x_74 == 0)
{
obj* x_118; obj* x_119; obj* x_121; 
lean::dec(x_72);
x_118 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_119 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
x_121 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_118, x_119, x_2);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; obj* x_124; uint32 x_127; obj* x_129; obj* x_131; obj* x_132; 
x_122 = lean::cnstr_get(x_121, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 2);
lean::inc(x_124);
lean::dec(x_121);
x_127 = 95;
lean::inc(x_1);
x_129 = lean::string_push(x_1, x_127);
lean::inc(x_6);
x_131 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_129, x_122);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_131);
if (lean::obj_tag(x_132) == 0)
{
obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_136 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_132);
x_137 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_136);
x_138 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_137);
return x_138;
}
else
{
obj* x_139; uint8 x_141; 
x_139 = lean::cnstr_get(x_132, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get_scalar<uint8>(x_132, sizeof(void*)*1);
x_113 = x_132;
x_114 = x_139;
x_115 = x_141;
goto lbl_116;
}
}
else
{
obj* x_142; uint8 x_144; obj* x_145; obj* x_147; obj* x_148; 
x_142 = lean::cnstr_get(x_121, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_145 = x_121;
} else {
 lean::dec(x_121);
 x_145 = lean::box(0);
}
lean::inc(x_142);
if (lean::is_scalar(x_145)) {
 x_147 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_147 = x_145;
}
lean::cnstr_set(x_147, 0, x_142);
lean::cnstr_set_scalar(x_147, sizeof(void*)*1, x_144);
x_148 = x_147;
x_113 = x_148;
x_114 = x_142;
x_115 = x_144;
goto lbl_116;
}
}
else
{
obj* x_153; obj* x_154; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_73);
x_153 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_72);
x_154 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_153);
return x_154;
}
lbl_116:
{
obj* x_155; obj* x_156; uint8 x_157; 
if (x_115 == 0)
{
obj* x_160; obj* x_161; obj* x_163; 
lean::dec(x_113);
x_160 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_161 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
x_163 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_160, x_161, x_2);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_166; obj* x_169; 
x_164 = lean::cnstr_get(x_163, 1);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_163, 2);
lean::inc(x_166);
lean::dec(x_163);
x_169 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_164);
if (lean::obj_tag(x_169) == 0)
{
obj* x_170; obj* x_172; obj* x_174; obj* x_177; 
x_170 = lean::cnstr_get(x_169, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_169, 1);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_169, 2);
lean::inc(x_174);
lean::dec(x_169);
x_177 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_172);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_180; obj* x_182; obj* x_185; obj* x_186; obj* x_188; uint32 x_191; obj* x_193; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_177, 1);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_177, 2);
lean::inc(x_182);
lean::dec(x_177);
x_185 = lean::mk_nat_obj(16u);
x_186 = lean::nat_mul(x_170, x_185);
lean::dec(x_170);
x_188 = lean::nat_add(x_186, x_178);
lean::dec(x_178);
lean::dec(x_186);
x_191 = l_char_of__nat(x_188);
lean::inc(x_1);
x_193 = lean::string_push(x_1, x_191);
lean::inc(x_6);
x_195 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_193, x_180);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_195);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_196);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_197);
if (lean::obj_tag(x_198) == 0)
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_202 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_198);
x_203 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_202);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_203);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_204);
return x_205;
}
else
{
obj* x_206; uint8 x_208; 
x_206 = lean::cnstr_get(x_198, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get_scalar<uint8>(x_198, sizeof(void*)*1);
x_155 = x_198;
x_156 = x_206;
x_157 = x_208;
goto lbl_158;
}
}
else
{
obj* x_210; uint8 x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_170);
x_210 = lean::cnstr_get(x_177, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*1);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 x_213 = x_177;
} else {
 lean::dec(x_177);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_210);
lean::cnstr_set_scalar(x_214, sizeof(void*)*1, x_212);
x_215 = x_214;
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_215);
x_217 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_216);
if (lean::obj_tag(x_217) == 0)
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_221 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_217);
x_222 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_221);
x_223 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_222);
x_224 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_223);
return x_224;
}
else
{
obj* x_225; uint8 x_227; 
x_225 = lean::cnstr_get(x_217, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get_scalar<uint8>(x_217, sizeof(void*)*1);
x_155 = x_217;
x_156 = x_225;
x_157 = x_227;
goto lbl_158;
}
}
}
else
{
obj* x_228; uint8 x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
x_228 = lean::cnstr_get(x_169, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get_scalar<uint8>(x_169, sizeof(void*)*1);
if (lean::is_exclusive(x_169)) {
 lean::cnstr_release(x_169, 0);
 x_231 = x_169;
} else {
 lean::dec(x_169);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_228);
lean::cnstr_set_scalar(x_232, sizeof(void*)*1, x_230);
x_233 = x_232;
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_233);
if (lean::obj_tag(x_234) == 0)
{
obj* x_238; obj* x_239; obj* x_240; obj* x_241; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_234);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_238);
x_240 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_239);
x_241 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_240);
return x_241;
}
else
{
obj* x_242; uint8 x_244; 
x_242 = lean::cnstr_get(x_234, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
x_155 = x_234;
x_156 = x_242;
x_157 = x_244;
goto lbl_158;
}
}
}
else
{
obj* x_245; uint8 x_247; obj* x_248; obj* x_250; obj* x_251; 
x_245 = lean::cnstr_get(x_163, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get_scalar<uint8>(x_163, sizeof(void*)*1);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 x_248 = x_163;
} else {
 lean::dec(x_163);
 x_248 = lean::box(0);
}
lean::inc(x_245);
if (lean::is_scalar(x_248)) {
 x_250 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_250 = x_248;
}
lean::cnstr_set(x_250, 0, x_245);
lean::cnstr_set_scalar(x_250, sizeof(void*)*1, x_247);
x_251 = x_250;
x_155 = x_251;
x_156 = x_245;
x_157 = x_247;
goto lbl_158;
}
}
else
{
obj* x_256; obj* x_257; obj* x_258; 
lean::dec(x_114);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_256 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_113);
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_256);
x_258 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_257);
return x_258;
}
lbl_158:
{
if (x_157 == 0)
{
obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_155);
x_260 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_261 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
x_262 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_260, x_261, x_2);
if (lean::obj_tag(x_262) == 0)
{
obj* x_263; obj* x_265; obj* x_268; 
x_263 = lean::cnstr_get(x_262, 1);
lean::inc(x_263);
x_265 = lean::cnstr_get(x_262, 2);
lean::inc(x_265);
lean::dec(x_262);
x_268 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_263);
if (lean::obj_tag(x_268) == 0)
{
obj* x_269; obj* x_271; obj* x_273; obj* x_276; 
x_269 = lean::cnstr_get(x_268, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_268, 2);
lean::inc(x_273);
lean::dec(x_268);
x_276 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_271);
if (lean::obj_tag(x_276) == 0)
{
obj* x_277; obj* x_279; obj* x_281; obj* x_284; 
x_277 = lean::cnstr_get(x_276, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_276, 1);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_276, 2);
lean::inc(x_281);
lean::dec(x_276);
x_284 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_279);
if (lean::obj_tag(x_284) == 0)
{
obj* x_285; obj* x_287; obj* x_289; obj* x_292; 
x_285 = lean::cnstr_get(x_284, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_284, 1);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_284, 2);
lean::inc(x_289);
lean::dec(x_284);
x_292 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_287);
if (lean::obj_tag(x_292) == 0)
{
obj* x_293; obj* x_295; obj* x_297; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_306; obj* x_309; obj* x_310; obj* x_312; obj* x_315; uint32 x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
x_293 = lean::cnstr_get(x_292, 0);
lean::inc(x_293);
x_295 = lean::cnstr_get(x_292, 1);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_292, 2);
lean::inc(x_297);
lean::dec(x_292);
x_300 = lean::mk_nat_obj(4096u);
x_301 = lean::nat_mul(x_269, x_300);
lean::dec(x_269);
x_303 = lean::mk_nat_obj(256u);
x_304 = lean::nat_mul(x_277, x_303);
lean::dec(x_277);
x_306 = lean::nat_add(x_301, x_304);
lean::dec(x_304);
lean::dec(x_301);
x_309 = lean::mk_nat_obj(16u);
x_310 = lean::nat_mul(x_285, x_309);
lean::dec(x_285);
x_312 = lean::nat_add(x_306, x_310);
lean::dec(x_310);
lean::dec(x_306);
x_315 = lean::nat_add(x_312, x_293);
lean::dec(x_293);
lean::dec(x_312);
x_318 = l_char_of__nat(x_315);
x_319 = lean::string_push(x_1, x_318);
x_320 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_319, x_295);
x_321 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_297, x_320);
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_289, x_321);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_281, x_322);
x_324 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_323);
x_325 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_324);
x_326 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_325);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_326);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_327);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_328);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_329);
return x_330;
}
else
{
obj* x_336; uint8 x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_285);
lean::dec(x_277);
lean::dec(x_269);
x_336 = lean::cnstr_get(x_292, 0);
lean::inc(x_336);
x_338 = lean::cnstr_get_scalar<uint8>(x_292, sizeof(void*)*1);
if (lean::is_exclusive(x_292)) {
 lean::cnstr_release(x_292, 0);
 x_339 = x_292;
} else {
 lean::dec(x_292);
 x_339 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_340 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_340 = x_339;
}
lean::cnstr_set(x_340, 0, x_336);
lean::cnstr_set_scalar(x_340, sizeof(void*)*1, x_338);
x_341 = x_340;
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_289, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_281, x_342);
x_344 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_343);
x_345 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_344);
x_346 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_345);
x_347 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_346);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_347);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_348);
x_350 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_349);
return x_350;
}
}
else
{
obj* x_355; uint8 x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_277);
lean::dec(x_269);
x_355 = lean::cnstr_get(x_284, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get_scalar<uint8>(x_284, sizeof(void*)*1);
if (lean::is_exclusive(x_284)) {
 lean::cnstr_release(x_284, 0);
 x_358 = x_284;
} else {
 lean::dec(x_284);
 x_358 = lean::box(0);
}
if (lean::is_scalar(x_358)) {
 x_359 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_359 = x_358;
}
lean::cnstr_set(x_359, 0, x_355);
lean::cnstr_set_scalar(x_359, sizeof(void*)*1, x_357);
x_360 = x_359;
x_361 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_281, x_360);
x_362 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_361);
x_363 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_362);
x_364 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_363);
x_365 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_364);
x_366 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_365);
x_367 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_366);
x_368 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_367);
return x_368;
}
}
else
{
obj* x_372; uint8 x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_269);
x_372 = lean::cnstr_get(x_276, 0);
lean::inc(x_372);
x_374 = lean::cnstr_get_scalar<uint8>(x_276, sizeof(void*)*1);
if (lean::is_exclusive(x_276)) {
 lean::cnstr_release(x_276, 0);
 x_375 = x_276;
} else {
 lean::dec(x_276);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_372);
lean::cnstr_set_scalar(x_376, sizeof(void*)*1, x_374);
x_377 = x_376;
x_378 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_377);
x_379 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_378);
x_380 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_379);
x_381 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_380);
x_382 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_381);
x_383 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_382);
x_384 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_383);
return x_384;
}
}
else
{
obj* x_387; uint8 x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; 
lean::dec(x_6);
lean::dec(x_1);
x_387 = lean::cnstr_get(x_268, 0);
lean::inc(x_387);
x_389 = lean::cnstr_get_scalar<uint8>(x_268, sizeof(void*)*1);
if (lean::is_exclusive(x_268)) {
 lean::cnstr_release(x_268, 0);
 x_390 = x_268;
} else {
 lean::dec(x_268);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_387);
lean::cnstr_set_scalar(x_391, sizeof(void*)*1, x_389);
x_392 = x_391;
x_393 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_392);
x_394 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_393);
x_395 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_394);
x_396 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_395);
x_397 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_396);
x_398 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_397);
return x_398;
}
}
else
{
obj* x_401; uint8 x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; 
lean::dec(x_6);
lean::dec(x_1);
x_401 = lean::cnstr_get(x_262, 0);
lean::inc(x_401);
x_403 = lean::cnstr_get_scalar<uint8>(x_262, sizeof(void*)*1);
if (lean::is_exclusive(x_262)) {
 lean::cnstr_release(x_262, 0);
 x_404 = x_262;
} else {
 lean::dec(x_262);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_401);
lean::cnstr_set_scalar(x_405, sizeof(void*)*1, x_403);
x_406 = x_405;
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_407);
x_409 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_408);
x_410 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_409);
x_411 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_410);
return x_411;
}
}
else
{
obj* x_416; obj* x_417; obj* x_418; obj* x_419; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_156);
x_416 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_114, x_155);
x_417 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_416);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_417);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_418);
return x_419;
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
obj* x_421; obj* x_422; 
lean::dec(x_0);
x_421 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_422 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_422, 0, x_1);
lean::cnstr_set(x_422, 1, x_2);
lean::cnstr_set(x_422, 2, x_421);
return x_422;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_string_join___closed__1;
x_3 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_1, x_2, x_0);
x_4 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_3);
return x_5;
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_string_demangle___closed__1;
x_2 = l_string_join___closed__1;
x_3 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_1, x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_6);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_1);
x_10 = x_9 == x_0;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_15, x_17, x_16, x_16, x_1);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::string_iterator_next(x_1);
x_22 = lean::box(0);
x_23 = lean::box_uint32(x_9);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set(x_24, 2, x_22);
return x_24;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__5(x_4, x_3, x_1);
return x_5;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__7(x_4, x_3, x_1);
return x_5;
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
uint32 x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_2);
x_6 = lean::string_iterator_remaining(x_1);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__9(x_6, x_5, x_1);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_10; obj* x_12; uint32 x_15; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_17 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_15, x_10);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_17);
return x_18;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_22 = x_7;
} else {
 lean::dec(x_7);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*1, x_21);
x_24 = x_23;
return x_24;
}
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = lean::string_iterator_curr(x_0);
x_26 = l_char_is__digit(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_31, x_33, x_32, x_32, x_0);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_34);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_39; obj* x_41; uint32 x_44; obj* x_46; obj* x_47; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 2);
lean::inc(x_41);
lean::dec(x_36);
x_44 = lean::unbox_uint32(x_37);
lean::dec(x_37);
x_46 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_44, x_39);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_46);
return x_47;
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get_scalar<uint8>(x_36, sizeof(void*)*1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_51 = x_36;
} else {
 lean::dec(x_36);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_48);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_50);
x_53 = x_52;
return x_53;
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::inc(x_0);
x_55 = lean::string_iterator_next(x_0);
x_56 = lean::box(0);
x_57 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_55);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_57);
return x_58;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = l_string_to__nat(x_2);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_10);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
return x_12;
}
else
{
obj* x_13; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_16 = x_1;
} else {
 lean::dec(x_1);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_15);
x_18 = x_17;
return x_18;
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
obj* x_4; obj* x_5; 
x_4 = l_string_join___closed__1;
x_5 = l___private_init_lean_parser_parsec_2__take__aux___main___rarg(x_0, x_4, x_1);
return x_5;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_7 = l_string_join___closed__1;
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
}
}
obj* l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_1 = l_match__failed___rarg___closed__1;
x_2 = l_mjoin___rarg___closed__1;
x_3 = l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
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
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 2);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
}
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_17;
}
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_20);
x_9 = x_21;
goto lbl_10;
}
else
{
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_25 = x_12;
} else {
 lean::dec(x_12);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_24);
x_27 = x_26;
x_9 = x_27;
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
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_31 = lean::cnstr_get(x_9, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_33 == 0)
{
obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_9);
x_39 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_40 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
x_42 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_39, x_40, x_2);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 lean::cnstr_release(x_42, 2);
 x_47 = x_42;
} else {
 lean::dec(x_42);
 x_47 = lean::box(0);
}
x_48 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_43);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_53; obj* x_56; 
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 2);
lean::inc(x_53);
lean::dec(x_48);
x_56 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_51);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_59; obj* x_62; 
x_57 = lean::cnstr_get(x_56, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 2);
lean::inc(x_59);
lean::dec(x_56);
x_62 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_49, x_57);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
lean::dec(x_62);
x_70 = l_lean_string_demangle(x_63);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_47;
}
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_65);
lean::cnstr_set(x_72, 2, x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; 
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 2);
lean::inc(x_78);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_81 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_76);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_84);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_89 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_85);
return x_89;
}
else
{
obj* x_90; uint8 x_92; 
x_90 = lean::cnstr_get(x_85, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
x_34 = x_85;
x_35 = x_90;
x_36 = x_92;
goto lbl_37;
}
}
else
{
obj* x_93; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_74, 0);
lean::inc(x_93);
lean::dec(x_74);
lean::inc(x_1);
x_97 = lean_name_mk_string(x_1, x_93);
lean::inc(x_6);
x_99 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_97, x_76);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_100);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_107; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_107 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_103);
return x_107;
}
else
{
obj* x_108; uint8 x_110; 
x_108 = lean::cnstr_get(x_103, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*1);
x_34 = x_103;
x_35 = x_108;
x_36 = x_110;
goto lbl_37;
}
}
}
else
{
obj* x_111; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_111 = lean::cnstr_get(x_73, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_114 = x_73;
} else {
 lean::dec(x_73);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_111);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = x_115;
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_116);
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_123; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_123 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_119);
return x_123;
}
else
{
obj* x_124; uint8 x_126; 
x_124 = lean::cnstr_get(x_119, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get_scalar<uint8>(x_119, sizeof(void*)*1);
x_34 = x_119;
x_35 = x_124;
x_36 = x_126;
goto lbl_37;
}
}
}
else
{
obj* x_128; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_47);
x_128 = lean::cnstr_get(x_62, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_131 = x_62;
} else {
 lean::dec(x_62);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_128);
lean::cnstr_set_scalar(x_132, sizeof(void*)*1, x_130);
x_133 = x_132;
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_140; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_140 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_136);
return x_140;
}
else
{
obj* x_141; uint8 x_143; 
x_141 = lean::cnstr_get(x_136, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
x_34 = x_136;
x_35 = x_141;
x_36 = x_143;
goto lbl_37;
}
}
}
else
{
obj* x_146; uint8 x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_47);
lean::dec(x_49);
x_146 = lean::cnstr_get(x_56, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_149 = x_56;
} else {
 lean::dec(x_56);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_146);
lean::cnstr_set_scalar(x_150, sizeof(void*)*1, x_148);
x_151 = x_150;
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_151);
x_153 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_152);
if (lean::obj_tag(x_153) == 0)
{
obj* x_157; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_157 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_153);
return x_157;
}
else
{
obj* x_158; uint8 x_160; 
x_158 = lean::cnstr_get(x_153, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get_scalar<uint8>(x_153, sizeof(void*)*1);
x_34 = x_153;
x_35 = x_158;
x_36 = x_160;
goto lbl_37;
}
}
}
else
{
obj* x_162; uint8 x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_47);
x_162 = lean::cnstr_get(x_48, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_165 = x_48;
} else {
 lean::dec(x_48);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_162);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_164);
x_167 = x_166;
x_168 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_172; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_172 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_168);
return x_172;
}
else
{
obj* x_173; uint8 x_175; 
x_173 = lean::cnstr_get(x_168, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
x_34 = x_168;
x_35 = x_173;
x_36 = x_175;
goto lbl_37;
}
}
}
else
{
obj* x_176; uint8 x_178; obj* x_179; obj* x_181; obj* x_182; 
x_176 = lean::cnstr_get(x_42, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_179 = x_42;
} else {
 lean::dec(x_42);
 x_179 = lean::box(0);
}
lean::inc(x_176);
if (lean::is_scalar(x_179)) {
 x_181 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_181 = x_179;
}
lean::cnstr_set(x_181, 0, x_176);
lean::cnstr_set_scalar(x_181, sizeof(void*)*1, x_178);
x_182 = x_181;
x_34 = x_182;
x_35 = x_176;
x_36 = x_178;
goto lbl_37;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_31);
return x_9;
}
lbl_37:
{
if (x_36 == 0)
{
obj* x_188; 
lean::dec(x_34);
x_188 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_2);
if (lean::obj_tag(x_188) == 0)
{
obj* x_189; obj* x_191; obj* x_194; 
x_189 = lean::cnstr_get(x_188, 1);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_188, 2);
lean::inc(x_191);
lean::dec(x_188);
x_194 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_189);
if (lean::obj_tag(x_194) == 0)
{
obj* x_195; obj* x_197; obj* x_199; obj* x_202; 
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_194, 2);
lean::inc(x_199);
lean::dec(x_194);
x_202 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_197);
if (lean::obj_tag(x_202) == 0)
{
obj* x_203; obj* x_205; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
x_203 = lean::cnstr_get(x_202, 1);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_202, 2);
lean::inc(x_205);
lean::dec(x_202);
x_208 = lean_name_mk_numeral(x_1, x_195);
x_209 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_208, x_203);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_205, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_199, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_211);
x_213 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_212);
x_214 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_213);
return x_214;
}
else
{
obj* x_218; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_195);
x_218 = lean::cnstr_get(x_202, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<uint8>(x_202, sizeof(void*)*1);
if (lean::is_exclusive(x_202)) {
 lean::cnstr_release(x_202, 0);
 x_221 = x_202;
} else {
 lean::dec(x_202);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_218);
lean::cnstr_set_scalar(x_222, sizeof(void*)*1, x_220);
x_223 = x_222;
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_199, x_223);
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_224);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_225);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_226);
return x_227;
}
}
else
{
obj* x_230; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
lean::dec(x_6);
lean::dec(x_1);
x_230 = lean::cnstr_get(x_194, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 x_233 = x_194;
} else {
 lean::dec(x_194);
 x_233 = lean::box(0);
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_230);
lean::cnstr_set_scalar(x_234, sizeof(void*)*1, x_232);
x_235 = x_234;
x_236 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_235);
x_237 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_237);
return x_238;
}
}
else
{
obj* x_241; uint8 x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_6);
lean::dec(x_1);
x_241 = lean::cnstr_get(x_188, 0);
lean::inc(x_241);
x_243 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*1);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 x_244 = x_188;
} else {
 lean::dec(x_188);
 x_244 = lean::box(0);
}
if (lean::is_scalar(x_244)) {
 x_245 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_245 = x_244;
}
lean::cnstr_set(x_245, 0, x_241);
lean::cnstr_set_scalar(x_245, sizeof(void*)*1, x_243);
x_246 = x_245;
x_247 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_246);
x_248 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_247);
return x_248;
}
}
else
{
obj* x_253; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_35);
x_253 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_34);
return x_253;
}
}
}
}
}
else
{
obj* x_255; obj* x_256; 
lean::dec(x_0);
x_255 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_256 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_256, 0, x_1);
lean::cnstr_set(x_256, 1, x_2);
lean::cnstr_set(x_256, 2, x_255);
return x_256;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::string_iterator_remaining(x_6);
x_12 = lean::box(0);
x_13 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_11, x_12, x_6);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_13);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_15);
return x_16;
}
else
{
obj* x_17; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_20 = x_5;
} else {
 lean::dec(x_5);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set_scalar(x_21, sizeof(void*)*1, x_19);
x_22 = x_21;
return x_22;
}
}
}
obj* l_lean_name_demangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_name__mangling_6__parse__mangled__name), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_string_join___closed__1;
x_4 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_2, x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
return x_10;
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
lean::mark_persistent(l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1);
 l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2);
 l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3 = _init_l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3();
lean::mark_persistent(l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3);
 l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1 = _init_l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1();
lean::mark_persistent(l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1);
 l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1 = _init_l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1);
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1);
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2);
 l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3 = _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3);
 l_lean_string_demangle___closed__1 = _init_l_lean_string_demangle___closed__1();
lean::mark_persistent(l_lean_string_demangle___closed__1);
 l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1);
 l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2 = _init_l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__2);
 l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1 = _init_l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1);
}
