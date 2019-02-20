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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = lean::unbox_uint32(x_7);
x_15 = lean::uint32_to_nat(x_14);
x_16 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
x_23 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_24 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_21, x_23);
return x_24;
}
else
{
obj* x_25; uint8 x_27; 
x_25 = lean::cnstr_get(x_21, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_1 = x_21;
x_2 = x_25;
x_3 = x_27;
goto lbl_4;
}
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_33; obj* x_34; 
x_28 = lean::cnstr_get(x_6, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_31 = x_6;
} else {
 lean::inc(x_28);
 lean::dec(x_6);
 x_31 = lean::box(0);
}
lean::inc(x_28);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_30);
x_34 = x_33;
x_1 = x_34;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
lbl_4:
{
obj* x_35; obj* x_36; uint8 x_37; 
if (x_3 == 0)
{
obj* x_40; uint8 x_42; 
lean::dec(x_1);
x_42 = lean::string_iterator_has_next(x_0);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_47; 
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_47 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_44, x_45, x_43, x_43, x_0);
x_40 = x_47;
goto lbl_41;
}
else
{
uint32 x_48; uint32 x_49; uint8 x_50; uint8 x_52; 
x_48 = lean::string_iterator_curr(x_0);
x_49 = 97;
x_52 = x_49 <= x_48;
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; 
x_53 = l_char_quote__core(x_48);
x_54 = l_char_has__repr___closed__1;
x_55 = lean::string_append(x_54, x_53);
lean::dec(x_53);
x_57 = lean::string_append(x_55, x_54);
x_58 = lean::box(0);
x_59 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_57, x_59, x_58, x_58, x_0);
x_40 = x_61;
goto lbl_41;
}
else
{
uint8 x_62; 
x_62 = 1;
x_50 = x_62;
goto lbl_51;
}
lbl_51:
{
uint32 x_63; uint8 x_64; 
x_63 = 102;
x_64 = x_48 <= x_63;
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; 
x_65 = l_char_quote__core(x_48);
x_66 = l_char_has__repr___closed__1;
x_67 = lean::string_append(x_66, x_65);
lean::dec(x_65);
x_69 = lean::string_append(x_67, x_66);
x_70 = lean::box(0);
x_71 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_73 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_69, x_71, x_70, x_70, x_0);
x_40 = x_73;
goto lbl_41;
}
else
{
if (x_50 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; 
x_74 = l_char_quote__core(x_48);
x_75 = l_char_has__repr___closed__1;
x_76 = lean::string_append(x_75, x_74);
lean::dec(x_74);
x_78 = lean::string_append(x_76, x_75);
x_79 = lean::box(0);
x_80 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
x_82 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_78, x_80, x_79, x_79, x_0);
x_40 = x_82;
goto lbl_41;
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::inc(x_0);
x_84 = lean::string_iterator_next(x_0);
x_85 = lean::box(0);
x_86 = lean::box_uint32(x_48);
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_84);
lean::cnstr_set(x_87, 2, x_85);
x_40 = x_87;
goto lbl_41;
}
}
}
}
lbl_41:
{
obj* x_88; obj* x_89; 
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_40);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_92; obj* x_94; obj* x_96; uint32 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_106; 
x_90 = lean::cnstr_get(x_89, 0);
x_92 = lean::cnstr_get(x_89, 1);
x_94 = lean::cnstr_get(x_89, 2);
if (lean::is_exclusive(x_89)) {
 x_96 = x_89;
} else {
 lean::inc(x_90);
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_89);
 x_96 = lean::box(0);
}
x_97 = lean::unbox_uint32(x_90);
x_98 = lean::uint32_to_nat(x_97);
x_99 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_100 = lean::nat_sub(x_98, x_99);
lean::dec(x_98);
x_102 = lean::mk_nat_obj(10u);
x_103 = lean::nat_add(x_102, x_100);
lean::dec(x_100);
if (lean::is_scalar(x_96)) {
 x_105 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_105 = x_96;
}
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_92);
lean::cnstr_set(x_105, 2, x_88);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_0);
x_108 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_106);
x_109 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_110 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_108, x_109);
return x_110;
}
else
{
obj* x_111; uint8 x_113; 
x_111 = lean::cnstr_get(x_106, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get_scalar<uint8>(x_106, sizeof(void*)*1);
x_35 = x_106;
x_36 = x_111;
x_37 = x_113;
goto lbl_38;
}
}
else
{
obj* x_114; uint8 x_116; obj* x_117; obj* x_119; obj* x_120; 
x_114 = lean::cnstr_get(x_89, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
if (lean::is_exclusive(x_89)) {
 x_117 = x_89;
} else {
 lean::inc(x_114);
 lean::dec(x_89);
 x_117 = lean::box(0);
}
lean::inc(x_114);
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_114);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_116);
x_120 = x_119;
x_35 = x_120;
x_36 = x_114;
x_37 = x_116;
goto lbl_38;
}
}
}
else
{
obj* x_123; obj* x_124; 
lean::dec(x_0);
lean::dec(x_2);
x_123 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_124 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_123);
return x_124;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_126; uint8 x_128; 
lean::dec(x_35);
x_128 = lean::string_iterator_has_next(x_0);
if (x_128 == 0)
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_129 = lean::box(0);
x_130 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_131 = l_mjoin___rarg___closed__1;
x_132 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_130, x_131, x_129, x_129, x_0);
x_126 = x_132;
goto lbl_127;
}
else
{
uint32 x_133; uint32 x_134; uint8 x_135; uint8 x_137; 
x_133 = lean::string_iterator_curr(x_0);
x_134 = 65;
x_137 = x_134 <= x_133;
if (x_137 == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_138 = l_char_quote__core(x_133);
x_139 = l_char_has__repr___closed__1;
x_140 = lean::string_append(x_139, x_138);
lean::dec(x_138);
x_142 = lean::string_append(x_140, x_139);
x_143 = lean::box(0);
x_144 = l_mjoin___rarg___closed__1;
x_145 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_142, x_144, x_143, x_143, x_0);
x_126 = x_145;
goto lbl_127;
}
else
{
uint8 x_146; 
x_146 = 1;
x_135 = x_146;
goto lbl_136;
}
lbl_136:
{
uint32 x_147; uint8 x_148; 
x_147 = 70;
x_148 = x_133 <= x_147;
if (x_148 == 0)
{
obj* x_149; obj* x_150; obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_149 = l_char_quote__core(x_133);
x_150 = l_char_has__repr___closed__1;
x_151 = lean::string_append(x_150, x_149);
lean::dec(x_149);
x_153 = lean::string_append(x_151, x_150);
x_154 = lean::box(0);
x_155 = l_mjoin___rarg___closed__1;
x_156 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_153, x_155, x_154, x_154, x_0);
x_126 = x_156;
goto lbl_127;
}
else
{
if (x_135 == 0)
{
obj* x_157; obj* x_158; obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_157 = l_char_quote__core(x_133);
x_158 = l_char_has__repr___closed__1;
x_159 = lean::string_append(x_158, x_157);
lean::dec(x_157);
x_161 = lean::string_append(x_159, x_158);
x_162 = lean::box(0);
x_163 = l_mjoin___rarg___closed__1;
x_164 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_161, x_163, x_162, x_162, x_0);
x_126 = x_164;
goto lbl_127;
}
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_165 = lean::string_iterator_next(x_0);
x_166 = lean::box(0);
x_167 = lean::box_uint32(x_133);
x_168 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
lean::cnstr_set(x_168, 2, x_166);
x_126 = x_168;
goto lbl_127;
}
}
}
}
lbl_127:
{
obj* x_169; obj* x_170; 
x_169 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_126);
if (lean::obj_tag(x_170) == 0)
{
obj* x_171; obj* x_173; obj* x_175; obj* x_177; uint32 x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_171 = lean::cnstr_get(x_170, 0);
x_173 = lean::cnstr_get(x_170, 1);
x_175 = lean::cnstr_get(x_170, 2);
if (lean::is_exclusive(x_170)) {
 x_177 = x_170;
} else {
 lean::inc(x_171);
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_170);
 x_177 = lean::box(0);
}
x_178 = lean::unbox_uint32(x_171);
x_179 = lean::uint32_to_nat(x_178);
x_180 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_181 = lean::nat_sub(x_179, x_180);
lean::dec(x_179);
x_183 = lean::mk_nat_obj(10u);
x_184 = lean::nat_add(x_183, x_181);
lean::dec(x_181);
if (lean::is_scalar(x_177)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_177;
}
lean::cnstr_set(x_186, 0, x_184);
lean::cnstr_set(x_186, 1, x_173);
lean::cnstr_set(x_186, 2, x_169);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_186);
x_188 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_187);
x_189 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_188);
x_190 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_191 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_189, x_190);
return x_191;
}
else
{
obj* x_192; uint8 x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_192 = lean::cnstr_get(x_170, 0);
x_194 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_exclusive(x_170)) {
 x_195 = x_170;
} else {
 lean::inc(x_192);
 lean::dec(x_170);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_192);
lean::cnstr_set_scalar(x_196, sizeof(void*)*1, x_194);
x_197 = x_196;
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_198);
x_200 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_201 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_199, x_200);
return x_201;
}
}
}
else
{
obj* x_204; obj* x_205; obj* x_206; 
lean::dec(x_36);
lean::dec(x_0);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_35);
x_205 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_206 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_204, x_205);
return x_206;
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
x_14 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_16 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
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
x_23 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_24 = x_11;
} else {
 lean::inc(x_21);
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
obj* x_37; obj* x_39; 
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_37 = x_8;
} else {
 lean::dec(x_8);
 x_37 = lean::box(0);
}
lean::inc(x_2);
x_39 = l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_43; obj* x_45; uint32 x_48; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_37);
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_39, 2);
lean::inc(x_45);
lean::dec(x_39);
x_48 = lean::unbox_uint32(x_41);
lean::inc(x_1);
x_50 = lean::string_push(x_1, x_48);
lean::inc(x_6);
x_52 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_50, x_43);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_52);
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
obj* x_61; uint8 x_63; obj* x_66; obj* x_67; 
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
lean::dec(x_39);
lean::inc(x_61);
if (lean::is_scalar(x_37)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_37;
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
obj* x_79; obj* x_81; obj* x_83; uint32 x_86; obj* x_88; obj* x_90; obj* x_91; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_86 = lean::unbox_uint32(x_79);
lean::inc(x_1);
x_88 = lean::string_push(x_1, x_86);
lean::inc(x_6);
x_90 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_88, x_81);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_95; obj* x_96; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_95 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_91);
x_96 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_95);
return x_96;
}
else
{
obj* x_97; uint8 x_99; 
x_97 = lean::cnstr_get(x_91, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
x_72 = x_91;
x_73 = x_97;
x_74 = x_99;
goto lbl_75;
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_105; obj* x_106; 
x_100 = lean::cnstr_get(x_78, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (lean::is_exclusive(x_78)) {
 x_103 = x_78;
} else {
 lean::inc(x_100);
 lean::dec(x_78);
 x_103 = lean::box(0);
}
lean::inc(x_100);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_100);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_102);
x_106 = x_105;
x_72 = x_106;
x_73 = x_100;
x_74 = x_102;
goto lbl_75;
}
}
else
{
obj* x_111; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_34);
x_111 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_33);
return x_111;
}
lbl_75:
{
obj* x_112; obj* x_113; uint8 x_114; 
if (x_74 == 0)
{
obj* x_117; obj* x_118; obj* x_120; 
lean::dec(x_72);
x_117 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_118 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
x_120 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_117, x_118, x_2);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_123; uint32 x_126; obj* x_128; obj* x_130; obj* x_131; 
x_121 = lean::cnstr_get(x_120, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 2);
lean::inc(x_123);
lean::dec(x_120);
x_126 = 95;
lean::inc(x_1);
x_128 = lean::string_push(x_1, x_126);
lean::inc(x_6);
x_130 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_128, x_121);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_130);
if (lean::obj_tag(x_131) == 0)
{
obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_135 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_131);
x_136 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_135);
x_137 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_136);
return x_137;
}
else
{
obj* x_138; uint8 x_140; 
x_138 = lean::cnstr_get(x_131, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get_scalar<uint8>(x_131, sizeof(void*)*1);
x_112 = x_131;
x_113 = x_138;
x_114 = x_140;
goto lbl_115;
}
}
else
{
obj* x_141; uint8 x_143; obj* x_144; obj* x_146; obj* x_147; 
x_141 = lean::cnstr_get(x_120, 0);
x_143 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (lean::is_exclusive(x_120)) {
 x_144 = x_120;
} else {
 lean::inc(x_141);
 lean::dec(x_120);
 x_144 = lean::box(0);
}
lean::inc(x_141);
if (lean::is_scalar(x_144)) {
 x_146 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_146 = x_144;
}
lean::cnstr_set(x_146, 0, x_141);
lean::cnstr_set_scalar(x_146, sizeof(void*)*1, x_143);
x_147 = x_146;
x_112 = x_147;
x_113 = x_141;
x_114 = x_143;
goto lbl_115;
}
}
else
{
obj* x_152; obj* x_153; 
lean::dec(x_73);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_152 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_72);
x_153 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_152);
return x_153;
}
lbl_115:
{
obj* x_154; obj* x_155; uint8 x_156; 
if (x_114 == 0)
{
obj* x_159; obj* x_160; obj* x_162; 
lean::dec(x_112);
x_159 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_160 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
x_162 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_159, x_160, x_2);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_165; obj* x_168; 
x_163 = lean::cnstr_get(x_162, 1);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 2);
lean::inc(x_165);
lean::dec(x_162);
x_168 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_163);
if (lean::obj_tag(x_168) == 0)
{
obj* x_169; obj* x_171; obj* x_173; obj* x_176; 
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_168, 2);
lean::inc(x_173);
lean::dec(x_168);
x_176 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_184; obj* x_185; obj* x_187; uint32 x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 2);
lean::inc(x_181);
lean::dec(x_176);
x_184 = lean::mk_nat_obj(16u);
x_185 = lean::nat_mul(x_169, x_184);
lean::dec(x_169);
x_187 = lean::nat_add(x_185, x_177);
lean::dec(x_177);
lean::dec(x_185);
x_190 = l_char_of__nat(x_187);
lean::inc(x_1);
x_192 = lean::string_push(x_1, x_190);
lean::inc(x_6);
x_194 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_192, x_179);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_195);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_196);
if (lean::obj_tag(x_197) == 0)
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_201 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_197);
x_202 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_201);
x_203 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_202);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_203);
return x_204;
}
else
{
obj* x_205; uint8 x_207; 
x_205 = lean::cnstr_get(x_197, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*1);
x_154 = x_197;
x_155 = x_205;
x_156 = x_207;
goto lbl_157;
}
}
else
{
obj* x_209; uint8 x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
lean::dec(x_169);
x_209 = lean::cnstr_get(x_176, 0);
x_211 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
 x_212 = x_176;
} else {
 lean::inc(x_209);
 lean::dec(x_176);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_209);
lean::cnstr_set_scalar(x_213, sizeof(void*)*1, x_211);
x_214 = x_213;
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_215);
if (lean::obj_tag(x_216) == 0)
{
obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_220 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_216);
x_221 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_220);
x_222 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_221);
x_223 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_222);
return x_223;
}
else
{
obj* x_224; uint8 x_226; 
x_224 = lean::cnstr_get(x_216, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
x_154 = x_216;
x_155 = x_224;
x_156 = x_226;
goto lbl_157;
}
}
}
else
{
obj* x_227; uint8 x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_227 = lean::cnstr_get(x_168, 0);
x_229 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_exclusive(x_168)) {
 x_230 = x_168;
} else {
 lean::inc(x_227);
 lean::dec(x_168);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_227);
lean::cnstr_set_scalar(x_231, sizeof(void*)*1, x_229);
x_232 = x_231;
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_232);
if (lean::obj_tag(x_233) == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_237 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_233);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_238);
x_240 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_239);
return x_240;
}
else
{
obj* x_241; uint8 x_243; 
x_241 = lean::cnstr_get(x_233, 0);
lean::inc(x_241);
x_243 = lean::cnstr_get_scalar<uint8>(x_233, sizeof(void*)*1);
x_154 = x_233;
x_155 = x_241;
x_156 = x_243;
goto lbl_157;
}
}
}
else
{
obj* x_244; uint8 x_246; obj* x_247; obj* x_249; obj* x_250; 
x_244 = lean::cnstr_get(x_162, 0);
x_246 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
if (lean::is_exclusive(x_162)) {
 x_247 = x_162;
} else {
 lean::inc(x_244);
 lean::dec(x_162);
 x_247 = lean::box(0);
}
lean::inc(x_244);
if (lean::is_scalar(x_247)) {
 x_249 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_249 = x_247;
}
lean::cnstr_set(x_249, 0, x_244);
lean::cnstr_set_scalar(x_249, sizeof(void*)*1, x_246);
x_250 = x_249;
x_154 = x_250;
x_155 = x_244;
x_156 = x_246;
goto lbl_157;
}
}
else
{
obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_113);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_255 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_112);
x_256 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_255);
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_256);
return x_257;
}
lbl_157:
{
if (x_156 == 0)
{
obj* x_259; obj* x_260; obj* x_261; 
lean::dec(x_154);
x_259 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_260 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
x_261 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_259, x_260, x_2);
if (lean::obj_tag(x_261) == 0)
{
obj* x_262; obj* x_264; obj* x_267; 
x_262 = lean::cnstr_get(x_261, 1);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_261, 2);
lean::inc(x_264);
lean::dec(x_261);
x_267 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_262);
if (lean::obj_tag(x_267) == 0)
{
obj* x_268; obj* x_270; obj* x_272; obj* x_275; 
x_268 = lean::cnstr_get(x_267, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_267, 1);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_267, 2);
lean::inc(x_272);
lean::dec(x_267);
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
obj* x_292; obj* x_294; obj* x_296; obj* x_299; obj* x_300; obj* x_302; obj* x_303; obj* x_305; obj* x_308; obj* x_309; obj* x_311; obj* x_314; uint32 x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
x_292 = lean::cnstr_get(x_291, 0);
lean::inc(x_292);
x_294 = lean::cnstr_get(x_291, 1);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_291, 2);
lean::inc(x_296);
lean::dec(x_291);
x_299 = lean::mk_nat_obj(4096u);
x_300 = lean::nat_mul(x_268, x_299);
lean::dec(x_268);
x_302 = lean::mk_nat_obj(256u);
x_303 = lean::nat_mul(x_276, x_302);
lean::dec(x_276);
x_305 = lean::nat_add(x_300, x_303);
lean::dec(x_303);
lean::dec(x_300);
x_308 = lean::mk_nat_obj(16u);
x_309 = lean::nat_mul(x_284, x_308);
lean::dec(x_284);
x_311 = lean::nat_add(x_305, x_309);
lean::dec(x_309);
lean::dec(x_305);
x_314 = lean::nat_add(x_311, x_292);
lean::dec(x_292);
lean::dec(x_311);
x_317 = l_char_of__nat(x_314);
x_318 = lean::string_push(x_1, x_317);
x_319 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_318, x_294);
x_320 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_296, x_319);
x_321 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_320);
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_321);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_322);
x_324 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_323);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_324);
x_326 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_325);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_326);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_327);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_328);
return x_329;
}
else
{
obj* x_335; uint8 x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_284);
lean::dec(x_276);
lean::dec(x_268);
x_335 = lean::cnstr_get(x_291, 0);
x_337 = lean::cnstr_get_scalar<uint8>(x_291, sizeof(void*)*1);
if (lean::is_exclusive(x_291)) {
 x_338 = x_291;
} else {
 lean::inc(x_335);
 lean::dec(x_291);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_335);
lean::cnstr_set_scalar(x_339, sizeof(void*)*1, x_337);
x_340 = x_339;
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_342);
x_344 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_343);
x_345 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_344);
x_346 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_345);
x_347 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_346);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_347);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_348);
return x_349;
}
}
else
{
obj* x_354; uint8 x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_276);
lean::dec(x_268);
x_354 = lean::cnstr_get(x_283, 0);
x_356 = lean::cnstr_get_scalar<uint8>(x_283, sizeof(void*)*1);
if (lean::is_exclusive(x_283)) {
 x_357 = x_283;
} else {
 lean::inc(x_354);
 lean::dec(x_283);
 x_357 = lean::box(0);
}
if (lean::is_scalar(x_357)) {
 x_358 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_358 = x_357;
}
lean::cnstr_set(x_358, 0, x_354);
lean::cnstr_set_scalar(x_358, sizeof(void*)*1, x_356);
x_359 = x_358;
x_360 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_359);
x_361 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_360);
x_362 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_361);
x_363 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_362);
x_364 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_363);
x_365 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_364);
x_366 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_365);
x_367 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_366);
return x_367;
}
}
else
{
obj* x_371; uint8 x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_268);
x_371 = lean::cnstr_get(x_275, 0);
x_373 = lean::cnstr_get_scalar<uint8>(x_275, sizeof(void*)*1);
if (lean::is_exclusive(x_275)) {
 x_374 = x_275;
} else {
 lean::inc(x_371);
 lean::dec(x_275);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_371);
lean::cnstr_set_scalar(x_375, sizeof(void*)*1, x_373);
x_376 = x_375;
x_377 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_376);
x_378 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_377);
x_379 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_378);
x_380 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_379);
x_381 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_380);
x_382 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_381);
x_383 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_382);
return x_383;
}
}
else
{
obj* x_386; uint8 x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
lean::dec(x_6);
lean::dec(x_1);
x_386 = lean::cnstr_get(x_267, 0);
x_388 = lean::cnstr_get_scalar<uint8>(x_267, sizeof(void*)*1);
if (lean::is_exclusive(x_267)) {
 x_389 = x_267;
} else {
 lean::inc(x_386);
 lean::dec(x_267);
 x_389 = lean::box(0);
}
if (lean::is_scalar(x_389)) {
 x_390 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_390 = x_389;
}
lean::cnstr_set(x_390, 0, x_386);
lean::cnstr_set_scalar(x_390, sizeof(void*)*1, x_388);
x_391 = x_390;
x_392 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_391);
x_393 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_392);
x_394 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_393);
x_395 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_394);
x_396 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_395);
x_397 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_396);
return x_397;
}
}
else
{
obj* x_400; uint8 x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; 
lean::dec(x_6);
lean::dec(x_1);
x_400 = lean::cnstr_get(x_261, 0);
x_402 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*1);
if (lean::is_exclusive(x_261)) {
 x_403 = x_261;
} else {
 lean::inc(x_400);
 lean::dec(x_261);
 x_403 = lean::box(0);
}
if (lean::is_scalar(x_403)) {
 x_404 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_404 = x_403;
}
lean::cnstr_set(x_404, 0, x_400);
lean::cnstr_set_scalar(x_404, sizeof(void*)*1, x_402);
x_405 = x_404;
x_406 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_155, x_405);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_407);
x_409 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_408);
x_410 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_409);
return x_410;
}
}
else
{
obj* x_415; obj* x_416; obj* x_417; obj* x_418; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_155);
x_415 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_113, x_154);
x_416 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_415);
x_417 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_416);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_417);
return x_418;
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
obj* x_420; obj* x_421; 
lean::dec(x_0);
x_420 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_421 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_421, 0, x_1);
lean::cnstr_set(x_421, 1, x_2);
lean::cnstr_set(x_421, 2, x_420);
return x_421;
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
obj* x_8; obj* x_10; obj* x_12; uint32 x_15; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 2);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::unbox_uint32(x_8);
x_16 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_15, x_10);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_21 = x_7;
} else {
 lean::inc(x_18);
 lean::dec(x_7);
 x_21 = lean::box(0);
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
else
{
uint32 x_24; uint8 x_25; 
x_24 = lean::string_iterator_curr(x_0);
x_25 = l_char_is__digit(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = l_char_quote__core(x_24);
x_27 = l_char_has__repr___closed__1;
x_28 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_30 = lean::string_append(x_28, x_27);
x_31 = lean::box(0);
x_32 = l_mjoin___rarg___closed__1;
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_30, x_32, x_31, x_31, x_0);
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_33);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_38; obj* x_40; uint32 x_43; obj* x_44; obj* x_45; 
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 2);
lean::inc(x_40);
lean::dec(x_35);
x_43 = lean::unbox_uint32(x_36);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_43, x_38);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_44);
return x_45;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_35, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 x_49 = x_35;
} else {
 lean::inc(x_46);
 lean::dec(x_35);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_48);
x_51 = x_50;
return x_51;
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::inc(x_0);
x_53 = lean::string_iterator_next(x_0);
x_54 = lean::box(0);
x_55 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_55);
return x_56;
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
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
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
x_15 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_16 = x_1;
} else {
 lean::inc(x_13);
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
x_15 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
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
x_24 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_25 = x_12;
} else {
 lean::inc(x_22);
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
obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_38 = x_9;
} else {
 lean::dec(x_9);
 x_38 = lean::box(0);
}
x_39 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_40 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
x_42 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_39, x_40, x_2);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_42, 1);
x_45 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_set(x_42, 1, lean::box(0));
 lean::cnstr_set(x_42, 2, lean::box(0));
 x_47 = x_42;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
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
obj* x_75; obj* x_77; obj* x_79; 
lean::dec(x_38);
x_75 = lean::cnstr_get(x_73, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_73, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_73, 2);
lean::inc(x_79);
lean::dec(x_73);
if (lean::obj_tag(x_75) == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_77);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_90 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; 
x_91 = lean::cnstr_get(x_86, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get_scalar<uint8>(x_86, sizeof(void*)*1);
x_34 = x_86;
x_35 = x_91;
x_36 = x_93;
goto lbl_37;
}
}
else
{
obj* x_94; obj* x_98; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = lean::cnstr_get(x_75, 0);
lean::inc(x_94);
lean::dec(x_75);
lean::inc(x_1);
x_98 = lean_name_mk_string(x_1, x_94);
lean::inc(x_6);
x_100 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_98, x_77);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_100);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_102);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_103);
if (lean::obj_tag(x_104) == 0)
{
obj* x_108; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_108 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_104);
return x_108;
}
else
{
obj* x_109; uint8 x_111; 
x_109 = lean::cnstr_get(x_104, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get_scalar<uint8>(x_104, sizeof(void*)*1);
x_34 = x_104;
x_35 = x_109;
x_36 = x_111;
goto lbl_37;
}
}
}
else
{
obj* x_112; uint8 x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_112 = lean::cnstr_get(x_73, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
lean::dec(x_73);
if (lean::is_scalar(x_38)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_38;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = x_116;
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_118);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_124; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_124 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_120);
return x_124;
}
else
{
obj* x_125; uint8 x_127; 
x_125 = lean::cnstr_get(x_120, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
x_34 = x_120;
x_35 = x_125;
x_36 = x_127;
goto lbl_37;
}
}
}
else
{
obj* x_129; uint8 x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_47);
x_129 = lean::cnstr_get(x_62, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
lean::dec(x_62);
if (lean::is_scalar(x_38)) {
 x_133 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_133 = x_38;
}
lean::cnstr_set(x_133, 0, x_129);
lean::cnstr_set_scalar(x_133, sizeof(void*)*1, x_131);
x_134 = x_133;
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_136);
if (lean::obj_tag(x_137) == 0)
{
obj* x_141; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_141 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_137);
return x_141;
}
else
{
obj* x_142; uint8 x_144; 
x_142 = lean::cnstr_get(x_137, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get_scalar<uint8>(x_137, sizeof(void*)*1);
x_34 = x_137;
x_35 = x_142;
x_36 = x_144;
goto lbl_37;
}
}
}
else
{
obj* x_147; uint8 x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_47);
lean::dec(x_49);
x_147 = lean::cnstr_get(x_56, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
lean::dec(x_56);
if (lean::is_scalar(x_38)) {
 x_151 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_151 = x_38;
}
lean::cnstr_set(x_151, 0, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*1, x_149);
x_152 = x_151;
x_153 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_152);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_158; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_158 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_154);
return x_158;
}
else
{
obj* x_159; uint8 x_161; 
x_159 = lean::cnstr_get(x_154, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get_scalar<uint8>(x_154, sizeof(void*)*1);
x_34 = x_154;
x_35 = x_159;
x_36 = x_161;
goto lbl_37;
}
}
}
else
{
obj* x_163; uint8 x_165; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_47);
x_163 = lean::cnstr_get(x_48, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
lean::dec(x_48);
if (lean::is_scalar(x_38)) {
 x_167 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_167 = x_38;
}
lean::cnstr_set(x_167, 0, x_163);
lean::cnstr_set_scalar(x_167, sizeof(void*)*1, x_165);
x_168 = x_167;
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_168);
if (lean::obj_tag(x_169) == 0)
{
obj* x_173; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_173 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_169);
return x_173;
}
else
{
obj* x_174; uint8 x_176; 
x_174 = lean::cnstr_get(x_169, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get_scalar<uint8>(x_169, sizeof(void*)*1);
x_34 = x_169;
x_35 = x_174;
x_36 = x_176;
goto lbl_37;
}
}
}
else
{
obj* x_177; uint8 x_179; obj* x_182; obj* x_183; 
x_177 = lean::cnstr_get(x_42, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
lean::dec(x_42);
lean::inc(x_177);
if (lean::is_scalar(x_38)) {
 x_182 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_182 = x_38;
}
lean::cnstr_set(x_182, 0, x_177);
lean::cnstr_set_scalar(x_182, sizeof(void*)*1, x_179);
x_183 = x_182;
x_34 = x_183;
x_35 = x_177;
x_36 = x_179;
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
obj* x_189; 
lean::dec(x_34);
x_189 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_2);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; obj* x_192; obj* x_195; 
x_190 = lean::cnstr_get(x_189, 1);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 2);
lean::inc(x_192);
lean::dec(x_189);
x_195 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_190);
if (lean::obj_tag(x_195) == 0)
{
obj* x_196; obj* x_198; obj* x_200; obj* x_203; 
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_195, 2);
lean::inc(x_200);
lean::dec(x_195);
x_203 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_8, x_198);
if (lean::obj_tag(x_203) == 0)
{
obj* x_204; obj* x_206; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
x_204 = lean::cnstr_get(x_203, 1);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 2);
lean::inc(x_206);
lean::dec(x_203);
x_209 = lean_name_mk_numeral(x_1, x_196);
x_210 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_209, x_204);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_206, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_212);
x_214 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_213);
x_215 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_214);
return x_215;
}
else
{
obj* x_219; uint8 x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_196);
x_219 = lean::cnstr_get(x_203, 0);
x_221 = lean::cnstr_get_scalar<uint8>(x_203, sizeof(void*)*1);
if (lean::is_exclusive(x_203)) {
 x_222 = x_203;
} else {
 lean::inc(x_219);
 lean::dec(x_203);
 x_222 = lean::box(0);
}
if (lean::is_scalar(x_222)) {
 x_223 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_223 = x_222;
}
lean::cnstr_set(x_223, 0, x_219);
lean::cnstr_set_scalar(x_223, sizeof(void*)*1, x_221);
x_224 = x_223;
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_224);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_225);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_226);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_227);
return x_228;
}
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_6);
lean::dec(x_1);
x_231 = lean::cnstr_get(x_195, 0);
x_233 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_exclusive(x_195)) {
 x_234 = x_195;
} else {
 lean::inc(x_231);
 lean::dec(x_195);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_238);
return x_239;
}
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_6);
lean::dec(x_1);
x_242 = lean::cnstr_get(x_189, 0);
x_244 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*1);
if (lean::is_exclusive(x_189)) {
 x_245 = x_189;
} else {
 lean::inc(x_242);
 lean::dec(x_189);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_242);
lean::cnstr_set_scalar(x_246, sizeof(void*)*1, x_244);
x_247 = x_246;
x_248 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_247);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_248);
return x_249;
}
}
else
{
obj* x_254; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_35);
x_254 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_34);
return x_254;
}
}
}
}
}
else
{
obj* x_256; obj* x_257; 
lean::dec(x_0);
x_256 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_257 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_257, 0, x_1);
lean::cnstr_set(x_257, 1, x_2);
lean::cnstr_set(x_257, 2, x_256);
return x_257;
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
x_19 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_20 = x_5;
} else {
 lean::inc(x_17);
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
