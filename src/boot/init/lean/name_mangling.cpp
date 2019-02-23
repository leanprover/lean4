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
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___boxed(obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1___boxed(obj*, obj*, obj*);
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
obj* l_id___rarg___boxed(obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___boxed(obj*);
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
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(uint32, obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_lean_name_mangle(obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
obj* l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(uint32, obj*);
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(obj*);
obj* l_lean_name_mangle___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___boxed(obj*);
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
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___boxed(obj*, obj*);
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
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
extern obj* l_match__failed___rarg___closed__1;
obj* l_lean_string_demangle(obj*);
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6___boxed(obj*, obj*);
obj* l_char_quote__core(uint32);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11___boxed(obj*);
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
obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint32 x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; uint32 x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; uint32 x_55; obj* x_57; obj* x_58; uint32 x_60; obj* x_62; obj* x_63; 
x_37 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_38 = lean::string_append(x_2, x_37);
x_39 = lean::mk_nat_obj(4096u);
x_40 = lean::nat_div(x_34, x_39);
x_41 = l_nat_digit__char(x_40);
lean::dec(x_40);
x_43 = lean::string_push(x_38, x_41);
x_44 = lean::nat_mod(x_34, x_39);
lean::dec(x_34);
x_46 = lean::mk_nat_obj(256u);
x_47 = lean::nat_div(x_44, x_46);
x_48 = l_nat_digit__char(x_47);
lean::dec(x_47);
x_50 = lean::string_push(x_43, x_48);
x_51 = lean::nat_mod(x_44, x_46);
lean::dec(x_44);
x_53 = lean::mk_nat_obj(16u);
x_54 = lean::nat_div(x_51, x_53);
x_55 = l_nat_digit__char(x_54);
lean::dec(x_54);
x_57 = lean::string_push(x_50, x_55);
x_58 = lean::nat_mod(x_51, x_53);
lean::dec(x_51);
x_60 = l_nat_digit__char(x_58);
lean::dec(x_58);
x_62 = lean::string_push(x_57, x_60);
x_63 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_63;
x_2 = x_62;
goto _start;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; uint32 x_69; obj* x_71; obj* x_72; uint32 x_74; obj* x_76; obj* x_77; 
x_65 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_66 = lean::string_append(x_2, x_65);
x_67 = lean::mk_nat_obj(16u);
x_68 = lean::nat_div(x_34, x_67);
x_69 = l_nat_digit__char(x_68);
lean::dec(x_68);
x_71 = lean::string_push(x_66, x_69);
x_72 = lean::nat_mod(x_34, x_67);
lean::dec(x_34);
x_74 = l_nat_digit__char(x_72);
lean::dec(x_72);
x_76 = lean::string_push(x_71, x_74);
x_77 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_77;
x_2 = x_76;
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
uint8 x_3; 
x_3 = l_string_is__empty(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_6; obj* x_8; 
x_4 = lean::string_length(x_0);
lean::inc(x_0);
x_6 = lean::string_mk_iterator(x_0);
lean::inc(x_2);
x_8 = l___private_init_lean_parser_parsec_1__str__aux___main(x_4, x_6, x_2);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
x_10 = lean::box(0);
x_11 = l_string_join___closed__1;
lean::inc(x_1);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_1);
lean::cnstr_set(x_13, 3, x_10);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_2);
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_24 = l_string_join___closed__1;
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_2);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_5 = l_option_get__or__else___main___rarg(x_2, x_4);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_3);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = x_11;
return x_12;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
lean::dec(x_15);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_18);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::string_iterator_next(x_0);
x_24 = lean::box(0);
x_25 = lean::box_uint32(x_9);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
return x_26;
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
x_46 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_44, x_45, x_43, x_43, x_0);
x_40 = x_46;
goto lbl_41;
}
else
{
uint32 x_47; uint32 x_48; uint8 x_49; uint8 x_51; 
x_47 = lean::string_iterator_curr(x_0);
x_48 = 97;
x_51 = x_48 <= x_47;
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_52 = l_char_quote__core(x_47);
x_53 = l_char_has__repr___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = lean::string_append(x_54, x_53);
x_57 = lean::box(0);
x_58 = l_mjoin___rarg___closed__1;
x_59 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_56, x_58, x_57, x_57, x_0);
lean::dec(x_56);
x_40 = x_59;
goto lbl_41;
}
else
{
uint8 x_61; 
x_61 = 1;
x_49 = x_61;
goto lbl_50;
}
lbl_50:
{
uint32 x_62; uint8 x_63; 
x_62 = 102;
x_63 = x_47 <= x_62;
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_64 = l_char_quote__core(x_47);
x_65 = l_char_has__repr___closed__1;
x_66 = lean::string_append(x_65, x_64);
lean::dec(x_64);
x_68 = lean::string_append(x_66, x_65);
x_69 = lean::box(0);
x_70 = l_mjoin___rarg___closed__1;
x_71 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_68, x_70, x_69, x_69, x_0);
lean::dec(x_68);
x_40 = x_71;
goto lbl_41;
}
else
{
if (x_49 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_73 = l_char_quote__core(x_47);
x_74 = l_char_has__repr___closed__1;
x_75 = lean::string_append(x_74, x_73);
lean::dec(x_73);
x_77 = lean::string_append(x_75, x_74);
x_78 = lean::box(0);
x_79 = l_mjoin___rarg___closed__1;
x_80 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_77, x_79, x_78, x_78, x_0);
lean::dec(x_77);
x_40 = x_80;
goto lbl_41;
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::inc(x_0);
x_83 = lean::string_iterator_next(x_0);
x_84 = lean::box(0);
x_85 = lean::box_uint32(x_47);
x_86 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_83);
lean::cnstr_set(x_86, 2, x_84);
x_40 = x_86;
goto lbl_41;
}
}
}
}
lbl_41:
{
obj* x_87; obj* x_88; 
x_87 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_40);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_93; obj* x_95; uint32 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_105; 
x_89 = lean::cnstr_get(x_88, 0);
x_91 = lean::cnstr_get(x_88, 1);
x_93 = lean::cnstr_get(x_88, 2);
if (lean::is_exclusive(x_88)) {
 x_95 = x_88;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_88);
 x_95 = lean::box(0);
}
x_96 = lean::unbox_uint32(x_89);
x_97 = lean::uint32_to_nat(x_96);
x_98 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_99 = lean::nat_sub(x_97, x_98);
lean::dec(x_97);
x_101 = lean::mk_nat_obj(10u);
x_102 = lean::nat_add(x_101, x_99);
lean::dec(x_99);
if (lean::is_scalar(x_95)) {
 x_104 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_104 = x_95;
}
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_91);
lean::cnstr_set(x_104, 2, x_87);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_104);
if (lean::obj_tag(x_105) == 0)
{
obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
x_107 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_105);
x_108 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_109 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_107, x_108);
return x_109;
}
else
{
obj* x_110; uint8 x_112; 
x_110 = lean::cnstr_get(x_105, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
x_35 = x_105;
x_36 = x_110;
x_37 = x_112;
goto lbl_38;
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_118; obj* x_119; 
x_113 = lean::cnstr_get(x_88, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 x_116 = x_88;
} else {
 lean::inc(x_113);
 lean::dec(x_88);
 x_116 = lean::box(0);
}
lean::inc(x_113);
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_113);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_115);
x_119 = x_118;
x_35 = x_119;
x_36 = x_113;
x_37 = x_115;
goto lbl_38;
}
}
}
else
{
obj* x_122; obj* x_123; 
lean::dec(x_0);
lean::dec(x_2);
x_122 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_123 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_122);
return x_123;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_125; uint8 x_127; 
lean::dec(x_35);
x_127 = lean::string_iterator_has_next(x_0);
if (x_127 == 0)
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_128 = lean::box(0);
x_129 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_130 = l_mjoin___rarg___closed__1;
x_131 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_129, x_130, x_128, x_128, x_0);
lean::dec(x_0);
x_125 = x_131;
goto lbl_126;
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
lean::dec(x_0);
lean::dec(x_142);
x_125 = x_145;
goto lbl_126;
}
else
{
uint8 x_148; 
x_148 = 1;
x_135 = x_148;
goto lbl_136;
}
lbl_136:
{
uint32 x_149; uint8 x_150; 
x_149 = 70;
x_150 = x_133 <= x_149;
if (x_150 == 0)
{
obj* x_151; obj* x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_151 = l_char_quote__core(x_133);
x_152 = l_char_has__repr___closed__1;
x_153 = lean::string_append(x_152, x_151);
lean::dec(x_151);
x_155 = lean::string_append(x_153, x_152);
x_156 = lean::box(0);
x_157 = l_mjoin___rarg___closed__1;
x_158 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_155, x_157, x_156, x_156, x_0);
lean::dec(x_0);
lean::dec(x_155);
x_125 = x_158;
goto lbl_126;
}
else
{
if (x_135 == 0)
{
obj* x_161; obj* x_162; obj* x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_161 = l_char_quote__core(x_133);
x_162 = l_char_has__repr___closed__1;
x_163 = lean::string_append(x_162, x_161);
lean::dec(x_161);
x_165 = lean::string_append(x_163, x_162);
x_166 = lean::box(0);
x_167 = l_mjoin___rarg___closed__1;
x_168 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_165, x_167, x_166, x_166, x_0);
lean::dec(x_0);
lean::dec(x_165);
x_125 = x_168;
goto lbl_126;
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
x_171 = lean::string_iterator_next(x_0);
x_172 = lean::box(0);
x_173 = lean::box_uint32(x_133);
x_174 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_174, 0, x_173);
lean::cnstr_set(x_174, 1, x_171);
lean::cnstr_set(x_174, 2, x_172);
x_125 = x_174;
goto lbl_126;
}
}
}
}
lbl_126:
{
obj* x_175; obj* x_176; 
x_175 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_125);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_183; uint32 x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_189; obj* x_190; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_177 = lean::cnstr_get(x_176, 0);
x_179 = lean::cnstr_get(x_176, 1);
x_181 = lean::cnstr_get(x_176, 2);
if (lean::is_exclusive(x_176)) {
 x_183 = x_176;
} else {
 lean::inc(x_177);
 lean::inc(x_179);
 lean::inc(x_181);
 lean::dec(x_176);
 x_183 = lean::box(0);
}
x_184 = lean::unbox_uint32(x_177);
x_185 = lean::uint32_to_nat(x_184);
x_186 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_187 = lean::nat_sub(x_185, x_186);
lean::dec(x_185);
x_189 = lean::mk_nat_obj(10u);
x_190 = lean::nat_add(x_189, x_187);
lean::dec(x_187);
if (lean::is_scalar(x_183)) {
 x_192 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_192 = x_183;
}
lean::cnstr_set(x_192, 0, x_190);
lean::cnstr_set(x_192, 1, x_179);
lean::cnstr_set(x_192, 2, x_175);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_192);
x_194 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_193);
x_195 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_194);
x_196 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_197 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_195, x_196);
return x_197;
}
else
{
obj* x_198; uint8 x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_198 = lean::cnstr_get(x_176, 0);
x_200 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
 x_201 = x_176;
} else {
 lean::inc(x_198);
 lean::dec(x_176);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_198);
lean::cnstr_set_scalar(x_202, sizeof(void*)*1, x_200);
x_203 = x_202;
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_203);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_204);
x_206 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_207 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_205, x_206);
return x_207;
}
}
}
else
{
obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_36);
lean::dec(x_0);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_35);
x_211 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
x_212 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_210, x_211);
return x_212;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_char_is__alpha(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
lean::dec(x_15);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_18);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::string_iterator_next(x_0);
x_24 = lean::box(0);
x_25 = lean::box_uint32(x_9);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
return x_26;
}
}
}
}
obj* _init_l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
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
uint32 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_5 = lean::string_iterator_curr(x_0);
x_6 = l_char_quote__core(x_5);
x_7 = l_char_has__repr___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = lean::string_append(x_8, x_7);
x_11 = lean::box(0);
x_12 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
x_13 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_10, x_12, x_11, x_11, x_0);
lean::dec(x_10);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; 
x_17 = lean::box(0);
x_18 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
lean::inc(x_0);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_0);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
}
}
obj* _init_l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_u");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
x_9 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_9, 1);
x_12 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_14)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_14;
}
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_10);
lean::cnstr_set(x_17, 2, x_15);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_17);
x_7 = x_18;
goto lbl_8;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_9, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_22 = x_9;
} else {
 lean::inc(x_19);
 lean::dec(x_9);
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
x_7 = x_24;
goto lbl_8;
}
lbl_8:
{
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; uint8 x_33; 
x_28 = lean::cnstr_get(x_7, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_30 == 0)
{
obj* x_37; 
lean::dec(x_7);
lean::inc(x_2);
x_37 = l_lean_parser_monad__parsec_alpha___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__5(x_2);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_42; uint32 x_45; obj* x_47; obj* x_48; obj* x_49; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 2);
lean::inc(x_42);
lean::dec(x_37);
x_45 = lean::unbox_uint32(x_38);
lean::inc(x_1);
x_47 = lean::string_push(x_1, x_45);
x_48 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_47, x_40);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_53; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_53 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_49);
return x_53;
}
else
{
obj* x_54; uint8 x_56; 
x_54 = lean::cnstr_get(x_49, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
x_31 = x_49;
x_32 = x_54;
x_33 = x_56;
goto lbl_34;
}
}
else
{
obj* x_57; uint8 x_59; obj* x_60; obj* x_62; obj* x_63; 
x_57 = lean::cnstr_get(x_37, 0);
x_59 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_60 = x_37;
} else {
 lean::inc(x_57);
 lean::dec(x_37);
 x_60 = lean::box(0);
}
lean::inc(x_57);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_57);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_59);
x_63 = x_62;
x_31 = x_63;
x_32 = x_57;
x_33 = x_59;
goto lbl_34;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_28);
return x_7;
}
lbl_34:
{
obj* x_68; obj* x_69; uint8 x_70; 
if (x_33 == 0)
{
obj* x_74; 
lean::dec(x_31);
lean::inc(x_2);
x_74 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; uint32 x_82; obj* x_84; obj* x_85; obj* x_86; 
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 2);
lean::inc(x_79);
lean::dec(x_74);
x_82 = lean::unbox_uint32(x_75);
lean::inc(x_1);
x_84 = lean::string_push(x_1, x_82);
x_85 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_84, x_77);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_91; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_90 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_86);
x_91 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_90);
return x_91;
}
else
{
obj* x_92; uint8 x_94; 
x_92 = lean::cnstr_get(x_86, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<uint8>(x_86, sizeof(void*)*1);
x_68 = x_86;
x_69 = x_92;
x_70 = x_94;
goto lbl_71;
}
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_100; obj* x_101; 
x_95 = lean::cnstr_get(x_74, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_98 = x_74;
} else {
 lean::inc(x_95);
 lean::dec(x_74);
 x_98 = lean::box(0);
}
lean::inc(x_95);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_95);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_97);
x_101 = x_100;
x_68 = x_101;
x_69 = x_95;
x_70 = x_97;
goto lbl_71;
}
}
else
{
obj* x_106; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_32);
x_106 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_31);
return x_106;
}
lbl_71:
{
obj* x_107; obj* x_108; uint8 x_109; 
if (x_70 == 0)
{
obj* x_112; obj* x_113; obj* x_115; 
lean::dec(x_68);
x_112 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_113 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
x_115 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_112, x_113, x_2);
if (lean::obj_tag(x_115) == 0)
{
obj* x_116; obj* x_118; uint32 x_121; obj* x_123; obj* x_124; obj* x_125; 
x_116 = lean::cnstr_get(x_115, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 2);
lean::inc(x_118);
lean::dec(x_115);
x_121 = 95;
lean::inc(x_1);
x_123 = lean::string_push(x_1, x_121);
x_124 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_123, x_116);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_129 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_125);
x_130 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_129);
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_130);
return x_131;
}
else
{
obj* x_132; uint8 x_134; 
x_132 = lean::cnstr_get(x_125, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*1);
x_107 = x_125;
x_108 = x_132;
x_109 = x_134;
goto lbl_110;
}
}
else
{
obj* x_135; uint8 x_137; obj* x_138; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_115, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_115, sizeof(void*)*1);
if (lean::is_exclusive(x_115)) {
 x_138 = x_115;
} else {
 lean::inc(x_135);
 lean::dec(x_115);
 x_138 = lean::box(0);
}
lean::inc(x_135);
if (lean::is_scalar(x_138)) {
 x_140 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_140 = x_138;
}
lean::cnstr_set(x_140, 0, x_135);
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_137);
x_141 = x_140;
x_107 = x_141;
x_108 = x_135;
x_109 = x_137;
goto lbl_110;
}
}
else
{
obj* x_146; obj* x_147; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_69);
x_146 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_68);
x_147 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_146);
return x_147;
}
lbl_110:
{
obj* x_148; obj* x_149; uint8 x_150; 
if (x_109 == 0)
{
obj* x_153; obj* x_154; obj* x_156; 
lean::dec(x_107);
x_153 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_154 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
x_156 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_153, x_154, x_2);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_159; obj* x_162; 
x_157 = lean::cnstr_get(x_156, 1);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 2);
lean::inc(x_159);
lean::dec(x_156);
x_162 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_157);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_165; obj* x_167; obj* x_170; 
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_162, 2);
lean::inc(x_167);
lean::dec(x_162);
x_170 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_165);
if (lean::obj_tag(x_170) == 0)
{
obj* x_171; obj* x_173; obj* x_175; obj* x_178; obj* x_179; obj* x_181; uint32 x_184; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_171 = lean::cnstr_get(x_170, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_170, 1);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_170, 2);
lean::inc(x_175);
lean::dec(x_170);
x_178 = lean::mk_nat_obj(16u);
x_179 = lean::nat_mul(x_163, x_178);
lean::dec(x_163);
x_181 = lean::nat_add(x_179, x_171);
lean::dec(x_171);
lean::dec(x_179);
x_184 = l_char_of__nat(x_181);
lean::dec(x_181);
lean::inc(x_1);
x_187 = lean::string_push(x_1, x_184);
x_188 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_187, x_173);
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_188);
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_189);
x_191 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_195 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_191);
x_196 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_195);
x_197 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_196);
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_197);
return x_198;
}
else
{
obj* x_199; uint8 x_201; 
x_199 = lean::cnstr_get(x_191, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*1);
x_148 = x_191;
x_149 = x_199;
x_150 = x_201;
goto lbl_151;
}
}
else
{
obj* x_203; uint8 x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_163);
x_203 = lean::cnstr_get(x_170, 0);
x_205 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_exclusive(x_170)) {
 x_206 = x_170;
} else {
 lean::inc(x_203);
 lean::dec(x_170);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_203);
lean::cnstr_set_scalar(x_207, sizeof(void*)*1, x_205);
x_208 = x_207;
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_208);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_214 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_210);
x_215 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_214);
x_216 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_215);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_216);
return x_217;
}
else
{
obj* x_218; uint8 x_220; 
x_218 = lean::cnstr_get(x_210, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<uint8>(x_210, sizeof(void*)*1);
x_148 = x_210;
x_149 = x_218;
x_150 = x_220;
goto lbl_151;
}
}
}
else
{
obj* x_221; uint8 x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
x_221 = lean::cnstr_get(x_162, 0);
x_223 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
if (lean::is_exclusive(x_162)) {
 x_224 = x_162;
} else {
 lean::inc(x_221);
 lean::dec(x_162);
 x_224 = lean::box(0);
}
if (lean::is_scalar(x_224)) {
 x_225 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_225 = x_224;
}
lean::cnstr_set(x_225, 0, x_221);
lean::cnstr_set_scalar(x_225, sizeof(void*)*1, x_223);
x_226 = x_225;
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_226);
if (lean::obj_tag(x_227) == 0)
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_227);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_231);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_232);
x_234 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_233);
return x_234;
}
else
{
obj* x_235; uint8 x_237; 
x_235 = lean::cnstr_get(x_227, 0);
lean::inc(x_235);
x_237 = lean::cnstr_get_scalar<uint8>(x_227, sizeof(void*)*1);
x_148 = x_227;
x_149 = x_235;
x_150 = x_237;
goto lbl_151;
}
}
}
else
{
obj* x_238; uint8 x_240; obj* x_241; obj* x_243; obj* x_244; 
x_238 = lean::cnstr_get(x_156, 0);
x_240 = lean::cnstr_get_scalar<uint8>(x_156, sizeof(void*)*1);
if (lean::is_exclusive(x_156)) {
 x_241 = x_156;
} else {
 lean::inc(x_238);
 lean::dec(x_156);
 x_241 = lean::box(0);
}
lean::inc(x_238);
if (lean::is_scalar(x_241)) {
 x_243 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_243 = x_241;
}
lean::cnstr_set(x_243, 0, x_238);
lean::cnstr_set_scalar(x_243, sizeof(void*)*1, x_240);
x_244 = x_243;
x_148 = x_244;
x_149 = x_238;
x_150 = x_240;
goto lbl_151;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_108);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_107);
x_250 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_249);
x_251 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_250);
return x_251;
}
lbl_151:
{
if (x_150 == 0)
{
obj* x_253; obj* x_254; obj* x_255; 
lean::dec(x_148);
x_253 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_254 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
x_255 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_253, x_254, x_2);
if (lean::obj_tag(x_255) == 0)
{
obj* x_256; obj* x_258; obj* x_261; 
x_256 = lean::cnstr_get(x_255, 1);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_255, 2);
lean::inc(x_258);
lean::dec(x_255);
x_261 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_256);
if (lean::obj_tag(x_261) == 0)
{
obj* x_262; obj* x_264; obj* x_266; obj* x_269; 
x_262 = lean::cnstr_get(x_261, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_261, 1);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_261, 2);
lean::inc(x_266);
lean::dec(x_261);
x_269 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_264);
if (lean::obj_tag(x_269) == 0)
{
obj* x_270; obj* x_272; obj* x_274; obj* x_277; 
x_270 = lean::cnstr_get(x_269, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_269, 1);
lean::inc(x_272);
x_274 = lean::cnstr_get(x_269, 2);
lean::inc(x_274);
lean::dec(x_269);
x_277 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_272);
if (lean::obj_tag(x_277) == 0)
{
obj* x_278; obj* x_280; obj* x_282; obj* x_285; 
x_278 = lean::cnstr_get(x_277, 0);
lean::inc(x_278);
x_280 = lean::cnstr_get(x_277, 1);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_277, 2);
lean::inc(x_282);
lean::dec(x_277);
x_285 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_280);
if (lean::obj_tag(x_285) == 0)
{
obj* x_286; obj* x_288; obj* x_290; obj* x_293; obj* x_294; obj* x_296; obj* x_297; obj* x_299; obj* x_302; obj* x_303; obj* x_305; obj* x_308; uint32 x_311; obj* x_313; obj* x_314; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; 
x_286 = lean::cnstr_get(x_285, 0);
lean::inc(x_286);
x_288 = lean::cnstr_get(x_285, 1);
lean::inc(x_288);
x_290 = lean::cnstr_get(x_285, 2);
lean::inc(x_290);
lean::dec(x_285);
x_293 = lean::mk_nat_obj(4096u);
x_294 = lean::nat_mul(x_262, x_293);
lean::dec(x_262);
x_296 = lean::mk_nat_obj(256u);
x_297 = lean::nat_mul(x_270, x_296);
lean::dec(x_270);
x_299 = lean::nat_add(x_294, x_297);
lean::dec(x_297);
lean::dec(x_294);
x_302 = lean::mk_nat_obj(16u);
x_303 = lean::nat_mul(x_278, x_302);
lean::dec(x_278);
x_305 = lean::nat_add(x_299, x_303);
lean::dec(x_303);
lean::dec(x_299);
x_308 = lean::nat_add(x_305, x_286);
lean::dec(x_286);
lean::dec(x_305);
x_311 = l_char_of__nat(x_308);
lean::dec(x_308);
x_313 = lean::string_push(x_1, x_311);
x_314 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_313, x_288);
lean::dec(x_6);
x_316 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_314);
x_317 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_316);
x_318 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_274, x_317);
x_319 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_318);
x_320 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_319);
x_321 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_320);
x_322 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_321);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_322);
x_324 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_323);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_324);
return x_325;
}
else
{
obj* x_331; uint8 x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_278);
lean::dec(x_270);
lean::dec(x_262);
x_331 = lean::cnstr_get(x_285, 0);
x_333 = lean::cnstr_get_scalar<uint8>(x_285, sizeof(void*)*1);
if (lean::is_exclusive(x_285)) {
 x_334 = x_285;
} else {
 lean::inc(x_331);
 lean::dec(x_285);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_331);
lean::cnstr_set_scalar(x_335, sizeof(void*)*1, x_333);
x_336 = x_335;
x_337 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_336);
x_338 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_274, x_337);
x_339 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_338);
x_340 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_339);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_340);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_341);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_343);
x_345 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_344);
return x_345;
}
}
else
{
obj* x_350; uint8 x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_270);
lean::dec(x_262);
x_350 = lean::cnstr_get(x_277, 0);
x_352 = lean::cnstr_get_scalar<uint8>(x_277, sizeof(void*)*1);
if (lean::is_exclusive(x_277)) {
 x_353 = x_277;
} else {
 lean::inc(x_350);
 lean::dec(x_277);
 x_353 = lean::box(0);
}
if (lean::is_scalar(x_353)) {
 x_354 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_354 = x_353;
}
lean::cnstr_set(x_354, 0, x_350);
lean::cnstr_set_scalar(x_354, sizeof(void*)*1, x_352);
x_355 = x_354;
x_356 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_274, x_355);
x_357 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_356);
x_358 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_357);
x_359 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_358);
x_360 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_359);
x_361 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_360);
x_362 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_361);
x_363 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_362);
return x_363;
}
}
else
{
obj* x_367; uint8 x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_262);
x_367 = lean::cnstr_get(x_269, 0);
x_369 = lean::cnstr_get_scalar<uint8>(x_269, sizeof(void*)*1);
if (lean::is_exclusive(x_269)) {
 x_370 = x_269;
} else {
 lean::inc(x_367);
 lean::dec(x_269);
 x_370 = lean::box(0);
}
if (lean::is_scalar(x_370)) {
 x_371 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_371 = x_370;
}
lean::cnstr_set(x_371, 0, x_367);
lean::cnstr_set_scalar(x_371, sizeof(void*)*1, x_369);
x_372 = x_371;
x_373 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_372);
x_374 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_373);
x_375 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_374);
x_376 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_375);
x_377 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_376);
x_378 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_377);
x_379 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_378);
return x_379;
}
}
else
{
obj* x_382; uint8 x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; 
lean::dec(x_6);
lean::dec(x_1);
x_382 = lean::cnstr_get(x_261, 0);
x_384 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*1);
if (lean::is_exclusive(x_261)) {
 x_385 = x_261;
} else {
 lean::inc(x_382);
 lean::dec(x_261);
 x_385 = lean::box(0);
}
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*1, x_384);
x_387 = x_386;
x_388 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_387);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_388);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_389);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_390);
x_392 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_391);
x_393 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_392);
return x_393;
}
}
else
{
obj* x_396; uint8 x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; 
lean::dec(x_6);
lean::dec(x_1);
x_396 = lean::cnstr_get(x_255, 0);
x_398 = lean::cnstr_get_scalar<uint8>(x_255, sizeof(void*)*1);
if (lean::is_exclusive(x_255)) {
 x_399 = x_255;
} else {
 lean::inc(x_396);
 lean::dec(x_255);
 x_399 = lean::box(0);
}
if (lean::is_scalar(x_399)) {
 x_400 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_400 = x_399;
}
lean::cnstr_set(x_400, 0, x_396);
lean::cnstr_set_scalar(x_400, sizeof(void*)*1, x_398);
x_401 = x_400;
x_402 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_401);
x_403 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_402);
x_404 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_403);
x_405 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_404);
x_406 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_405);
return x_406;
}
}
else
{
obj* x_411; obj* x_412; obj* x_413; obj* x_414; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_149);
x_411 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_148);
x_412 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_411);
x_413 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_32, x_412);
x_414 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_28, x_413);
return x_414;
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
obj* x_415; obj* x_416; 
x_415 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_416 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_416, 0, x_1);
lean::cnstr_set(x_416, 1, x_2);
lean::cnstr_set(x_416, 2, x_415);
return x_416;
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* l___private_init_lean_name__mangling_2__parse__mangled__string__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_3__parse__mangled__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_string_join___closed__1;
x_3 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_1, x_2, x_0);
lean::dec(x_1);
x_5 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
x_6 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_3);
return x_6;
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
lean::inc(x_0);
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
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__name_mangle__aux(x_0, x_1);
lean::dec(x_0);
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
obj* l_lean_name_mangle___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_name_mangle(x_0, x_1);
lean::dec(x_1);
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
lean::dec(x_1);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_9 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_1);
x_11 = x_10 == x_0;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_12 = l_char_quote__core(x_10);
x_13 = l_char_has__repr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_16, x_18, x_17, x_17, x_1);
lean::dec(x_1);
lean::dec(x_16);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_19);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::string_iterator_next(x_1);
x_25 = lean::box(0);
x_26 = lean::box_uint32(x_10);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_25);
return x_27;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_0, x_16);
lean::dec(x_0);
x_19 = lean::string_push(x_1, x_10);
x_20 = lean::string_iterator_next(x_2);
x_0 = x_17;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_23;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_0, x_16);
lean::dec(x_0);
x_19 = lean::string_push(x_1, x_10);
x_20 = lean::string_iterator_next(x_2);
x_0 = x_17;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_23;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_char_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_0, x_16);
lean::dec(x_0);
x_19 = lean::string_push(x_1, x_10);
x_20 = lean::string_iterator_next(x_2);
x_0 = x_17;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_string_join___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__9(x_5, x_4, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__3(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; uint32 x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::unbox_uint32(x_9);
x_17 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__4(x_16, x_11);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_17);
return x_18;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_8, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_22 = x_8;
} else {
 lean::inc(x_19);
 lean::dec(x_8);
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
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_31, x_33, x_32, x_32, x_0);
lean::dec(x_0);
lean::dec(x_31);
x_37 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_34);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_43; uint32 x_46; obj* x_47; obj* x_48; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_46 = lean::unbox_uint32(x_39);
x_47 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__6(x_46, x_41);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_47);
return x_48;
}
else
{
obj* x_49; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_49 = lean::cnstr_get(x_38, 0);
x_51 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 x_52 = x_38;
} else {
 lean::inc(x_49);
 lean::dec(x_38);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_51);
x_54 = x_53;
return x_54;
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; 
lean::inc(x_0);
x_56 = lean::string_iterator_next(x_0);
x_57 = lean::box(0);
x_58 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_56);
lean::dec(x_0);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_58);
return x_60;
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
obj* x_1; obj* x_2; obj* x_3; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; 
x_1 = l_match__failed___rarg___closed__1;
x_2 = l_mjoin___rarg___closed__1;
x_3 = l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_3);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*1, x_6);
x_8 = x_7;
return x_8;
}
}
obj* _init_l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_s");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* x_5; obj* x_6; uint32 x_7; obj* x_8; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
x_7 = 95;
x_10 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_10, 1);
x_13 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_16);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_18);
x_8 = x_19;
goto lbl_9;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_10, 0);
x_22 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_23 = x_10;
} else {
 lean::inc(x_20);
 lean::dec(x_10);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
x_8 = x_25;
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
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_29 = lean::cnstr_get(x_8, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_8);
x_37 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_38 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
x_40 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_37, x_38, x_2);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_46; 
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_41);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; obj* x_54; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_54 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_7, x_49);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_60; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_47, x_55);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_61 = lean::cnstr_get(x_60, 0);
x_63 = lean::cnstr_get(x_60, 1);
x_65 = lean::cnstr_get(x_60, 2);
if (lean::is_exclusive(x_60)) {
 x_67 = x_60;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = l_lean_string_demangle(x_61);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_67)) {
 x_70 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_70 = x_67;
}
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_63);
lean::cnstr_set(x_70, 2, x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; 
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 2);
lean::inc(x_76);
lean::dec(x_71);
x_79 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_74);
lean::dec(x_74);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_88; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_88 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_84);
return x_88;
}
else
{
obj* x_89; uint8 x_91; 
x_89 = lean::cnstr_get(x_84, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get_scalar<uint8>(x_84, sizeof(void*)*1);
x_32 = x_84;
x_33 = x_89;
x_34 = x_91;
goto lbl_35;
}
}
else
{
obj* x_92; obj* x_94; obj* x_97; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_92 = lean::cnstr_get(x_71, 1);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_71, 2);
lean::inc(x_94);
lean::dec(x_71);
x_97 = lean::cnstr_get(x_72, 0);
lean::inc(x_97);
lean::dec(x_72);
lean::inc(x_1);
x_101 = lean_name_mk_string(x_1, x_97);
x_102 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_101, x_92);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_102);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_103);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_104);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_110; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_110 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_106);
return x_110;
}
else
{
obj* x_111; uint8 x_113; 
x_111 = lean::cnstr_get(x_106, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get_scalar<uint8>(x_106, sizeof(void*)*1);
x_32 = x_106;
x_33 = x_111;
x_34 = x_113;
goto lbl_35;
}
}
}
else
{
obj* x_114; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_114 = lean::cnstr_get(x_71, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_117 = x_71;
} else {
 lean::inc(x_114);
 lean::dec(x_71);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_114);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_116);
x_119 = x_118;
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_119);
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_126; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_126 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_122);
return x_126;
}
else
{
obj* x_127; uint8 x_129; 
x_127 = lean::cnstr_get(x_122, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_122, sizeof(void*)*1);
x_32 = x_122;
x_33 = x_127;
x_34 = x_129;
goto lbl_35;
}
}
}
else
{
obj* x_130; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_130 = lean::cnstr_get(x_60, 0);
x_132 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
if (lean::is_exclusive(x_60)) {
 x_133 = x_60;
} else {
 lean::inc(x_130);
 lean::dec(x_60);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_130);
lean::cnstr_set_scalar(x_134, sizeof(void*)*1, x_132);
x_135 = x_134;
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_136);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_142; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_142 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_138);
return x_142;
}
else
{
obj* x_143; uint8 x_145; 
x_143 = lean::cnstr_get(x_138, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get_scalar<uint8>(x_138, sizeof(void*)*1);
x_32 = x_138;
x_33 = x_143;
x_34 = x_145;
goto lbl_35;
}
}
}
else
{
obj* x_147; uint8 x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_47);
x_147 = lean::cnstr_get(x_54, 0);
x_149 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_150 = x_54;
} else {
 lean::inc(x_147);
 lean::dec(x_54);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*1, x_149);
x_152 = x_151;
x_153 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_152);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_158; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_158 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_154);
return x_158;
}
else
{
obj* x_159; uint8 x_161; 
x_159 = lean::cnstr_get(x_154, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get_scalar<uint8>(x_154, sizeof(void*)*1);
x_32 = x_154;
x_33 = x_159;
x_34 = x_161;
goto lbl_35;
}
}
}
else
{
obj* x_162; uint8 x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_162 = lean::cnstr_get(x_46, 0);
x_164 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 x_165 = x_46;
} else {
 lean::inc(x_162);
 lean::dec(x_46);
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
x_168 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_172; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_172 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_168);
return x_172;
}
else
{
obj* x_173; uint8 x_175; 
x_173 = lean::cnstr_get(x_168, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
x_32 = x_168;
x_33 = x_173;
x_34 = x_175;
goto lbl_35;
}
}
}
else
{
obj* x_176; uint8 x_178; obj* x_179; obj* x_181; obj* x_182; 
x_176 = lean::cnstr_get(x_40, 0);
x_178 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 x_179 = x_40;
} else {
 lean::inc(x_176);
 lean::dec(x_40);
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
x_32 = x_182;
x_33 = x_176;
x_34 = x_178;
goto lbl_35;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_29);
return x_8;
}
lbl_35:
{
if (x_34 == 0)
{
obj* x_188; 
lean::dec(x_32);
x_188 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_7, x_2);
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
x_202 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_7, x_197);
if (lean::obj_tag(x_202) == 0)
{
obj* x_203; obj* x_205; obj* x_208; obj* x_209; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
x_203 = lean::cnstr_get(x_202, 1);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_202, 2);
lean::inc(x_205);
lean::dec(x_202);
x_208 = lean_name_mk_numeral(x_1, x_195);
x_209 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_6, x_208, x_203);
lean::dec(x_6);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_205, x_209);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_199, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_212);
x_214 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_213);
x_215 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_214);
return x_215;
}
else
{
obj* x_219; uint8 x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_195);
x_219 = lean::cnstr_get(x_202, 0);
x_221 = lean::cnstr_get_scalar<uint8>(x_202, sizeof(void*)*1);
if (lean::is_exclusive(x_202)) {
 x_222 = x_202;
} else {
 lean::inc(x_219);
 lean::dec(x_202);
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
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_199, x_224);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_225);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_226);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_227);
return x_228;
}
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_6);
lean::dec(x_1);
x_231 = lean::cnstr_get(x_194, 0);
x_233 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_exclusive(x_194)) {
 x_234 = x_194;
} else {
 lean::inc(x_231);
 lean::dec(x_194);
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
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_238);
return x_239;
}
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_6);
lean::dec(x_1);
x_242 = lean::cnstr_get(x_188, 0);
x_244 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*1);
if (lean::is_exclusive(x_188)) {
 x_245 = x_188;
} else {
 lean::inc(x_242);
 lean::dec(x_188);
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
x_248 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_247);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_248);
return x_249;
}
}
else
{
obj* x_254; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_33);
x_254 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_32);
return x_254;
}
}
}
}
}
else
{
obj* x_255; obj* x_256; 
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__8(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_0, x_1, x_2);
lean::dec(x_0);
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
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_6__parse__mangled__name(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = l_string_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_0, x_4, x_1);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_5, 2);
lean::inc(x_9);
lean::dec(x_5);
x_12 = lean::string_iterator_remaining(x_7);
x_13 = lean::box(0);
x_14 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_12, x_13, x_7);
lean::dec(x_12);
x_16 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_14);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_17);
return x_18;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_5, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_22 = x_5;
} else {
 lean::inc(x_19);
 lean::dec(x_5);
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
