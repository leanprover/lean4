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
obj* l_nat_digit__char(obj*);
obj* l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_name_demangle(obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parse__mangled__name__aux(obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
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
uint8 nat_dec_le(obj*, obj*);
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
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
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
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::mk_nat_obj(95u);
x_16 = lean::box_uint32(x_10);
x_17 = lean::nat_dec_eq(x_16, x_15);
lean::dec(x_15);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_20; 
x_20 = lean::box(0);
x_11 = x_20;
goto lbl_12;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::string_iterator_next(x_1);
x_22 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_23 = lean::string_append(x_2, x_22);
x_0 = x_7;
x_1 = x_21;
x_2 = x_23;
goto _start;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::string_iterator_next(x_1);
x_26 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_25;
x_2 = x_26;
goto _start;
}
}
else
{
if (x_13 == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::mk_nat_obj(95u);
x_29 = lean::box_uint32(x_10);
x_30 = lean::nat_dec_eq(x_29, x_28);
lean::dec(x_28);
lean::dec(x_29);
if (x_30 == 0)
{
obj* x_33; 
x_33 = lean::box(0);
x_11 = x_33;
goto lbl_12;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::string_iterator_next(x_1);
x_35 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_36 = lean::string_append(x_2, x_35);
x_0 = x_7;
x_1 = x_34;
x_2 = x_36;
goto _start;
}
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::string_iterator_next(x_1);
x_39 = lean::string_push(x_2, x_10);
x_0 = x_7;
x_1 = x_38;
x_2 = x_39;
goto _start;
}
}
lbl_12:
{
obj* x_42; obj* x_43; uint8 x_44; 
lean::dec(x_11);
x_42 = lean::mk_nat_obj(255u);
x_43 = lean::box_uint32(x_10);
x_44 = lean::nat_dec_lt(x_43, x_42);
lean::dec(x_42);
if (x_44 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; uint32 x_51; obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; uint32 x_60; obj* x_62; obj* x_63; obj* x_66; obj* x_67; obj* x_68; uint32 x_69; obj* x_71; obj* x_72; obj* x_75; uint32 x_76; obj* x_78; obj* x_79; 
x_46 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_47 = lean::string_append(x_2, x_46);
x_48 = lean::mk_nat_obj(4096u);
x_49 = lean::nat_div(x_43, x_48);
x_50 = l_nat_digit__char(x_49);
x_51 = lean::unbox_uint32(x_50);
lean::dec(x_50);
x_53 = lean::string_push(x_47, x_51);
x_54 = lean::nat_mod(x_43, x_48);
lean::dec(x_48);
lean::dec(x_43);
x_57 = lean::mk_nat_obj(256u);
x_58 = lean::nat_div(x_54, x_57);
x_59 = l_nat_digit__char(x_58);
x_60 = lean::unbox_uint32(x_59);
lean::dec(x_59);
x_62 = lean::string_push(x_53, x_60);
x_63 = lean::nat_mod(x_54, x_57);
lean::dec(x_57);
lean::dec(x_54);
x_66 = lean::mk_nat_obj(16u);
x_67 = lean::nat_div(x_63, x_66);
x_68 = l_nat_digit__char(x_67);
x_69 = lean::unbox_uint32(x_68);
lean::dec(x_68);
x_71 = lean::string_push(x_62, x_69);
x_72 = lean::nat_mod(x_63, x_66);
lean::dec(x_66);
lean::dec(x_63);
x_75 = l_nat_digit__char(x_72);
x_76 = lean::unbox_uint32(x_75);
lean::dec(x_75);
x_78 = lean::string_push(x_71, x_76);
x_79 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_79;
x_2 = x_78;
goto _start;
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; uint32 x_86; obj* x_88; obj* x_89; obj* x_92; uint32 x_93; obj* x_95; obj* x_96; 
x_81 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_82 = lean::string_append(x_2, x_81);
x_83 = lean::mk_nat_obj(16u);
x_84 = lean::nat_div(x_43, x_83);
x_85 = l_nat_digit__char(x_84);
x_86 = lean::unbox_uint32(x_85);
lean::dec(x_85);
x_88 = lean::string_push(x_82, x_86);
x_89 = lean::nat_mod(x_43, x_83);
lean::dec(x_83);
lean::dec(x_43);
x_92 = l_nat_digit__char(x_89);
x_93 = lean::unbox_uint32(x_92);
lean::dec(x_92);
x_95 = lean::string_push(x_88, x_93);
x_96 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_96;
x_2 = x_95;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_20; obj* x_21; 
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
x_15 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; 
lean::dec(x_0);
x_23 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_23);
x_25 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_21, x_23);
return x_25;
}
else
{
obj* x_26; uint8 x_28; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_1 = x_21;
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
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_32 = x_6;
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
obj* x_44; obj* x_45; obj* x_46; obj* x_51; 
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_44);
lean::inc(x_46);
lean::inc(x_45);
x_51 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_45, x_46, x_44, x_44, x_0);
x_41 = x_51;
goto lbl_42;
}
else
{
uint32 x_52; uint8 x_53; obj* x_55; obj* x_56; uint8 x_57; 
x_52 = lean::string_iterator_curr(x_0);
x_55 = lean::mk_nat_obj(97u);
x_56 = lean::box_uint32(x_52);
x_57 = lean::nat_dec_le(x_55, x_56);
lean::dec(x_56);
lean::dec(x_55);
if (x_57 == 0)
{
obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_71; 
x_60 = l_char_quote__core(x_52);
x_61 = l_char_has__repr___closed__1;
lean::inc(x_61);
x_63 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_65 = lean::string_append(x_63, x_61);
x_66 = lean::box(0);
x_67 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_66);
lean::inc(x_67);
x_71 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_65, x_67, x_66, x_66, x_0);
x_41 = x_71;
goto lbl_42;
}
else
{
uint8 x_72; 
x_72 = 1;
x_53 = x_72;
goto lbl_54;
}
lbl_54:
{
obj* x_73; obj* x_74; uint8 x_75; 
x_73 = lean::mk_nat_obj(102u);
x_74 = lean::box_uint32(x_52);
x_75 = lean::nat_dec_le(x_74, x_73);
lean::dec(x_73);
if (x_75 == 0)
{
obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_89; 
lean::dec(x_74);
x_78 = l_char_quote__core(x_52);
x_79 = l_char_has__repr___closed__1;
lean::inc(x_79);
x_81 = lean::string_append(x_79, x_78);
lean::dec(x_78);
x_83 = lean::string_append(x_81, x_79);
x_84 = lean::box(0);
x_85 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_84);
lean::inc(x_85);
x_89 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_83, x_85, x_84, x_84, x_0);
x_41 = x_89;
goto lbl_42;
}
else
{
if (x_53 == 0)
{
obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_102; 
lean::dec(x_74);
x_91 = l_char_quote__core(x_52);
x_92 = l_char_has__repr___closed__1;
lean::inc(x_92);
x_94 = lean::string_append(x_92, x_91);
lean::dec(x_91);
x_96 = lean::string_append(x_94, x_92);
x_97 = lean::box(0);
x_98 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_97);
lean::inc(x_98);
x_102 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_96, x_98, x_97, x_97, x_0);
x_41 = x_102;
goto lbl_42;
}
else
{
obj* x_104; obj* x_105; obj* x_106; 
lean::inc(x_0);
x_104 = lean::string_iterator_next(x_0);
x_105 = lean::box(0);
x_106 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_106, 0, x_74);
lean::cnstr_set(x_106, 1, x_104);
lean::cnstr_set(x_106, 2, x_105);
x_41 = x_106;
goto lbl_42;
}
}
}
}
lbl_42:
{
obj* x_107; obj* x_109; 
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_107, x_41);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_121; obj* x_122; obj* x_126; obj* x_127; 
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 2);
lean::inc(x_114);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 lean::cnstr_release(x_109, 2);
 x_116 = x_109;
}
x_117 = lean::mk_nat_obj(97u);
x_118 = lean::nat_sub(x_110, x_117);
lean::dec(x_117);
lean::dec(x_110);
x_121 = lean::mk_nat_obj(10u);
x_122 = lean::nat_add(x_121, x_118);
lean::dec(x_118);
lean::dec(x_121);
lean::inc(x_107);
if (lean::is_scalar(x_116)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_116;
}
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set(x_126, 1, x_112);
lean::cnstr_set(x_126, 2, x_107);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_129; obj* x_130; obj* x_132; 
lean::dec(x_0);
x_129 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_127);
x_130 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_130);
x_132 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_129, x_130);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_127, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
x_36 = x_127;
x_37 = x_133;
x_38 = x_135;
goto lbl_39;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_109, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_139 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_139 = x_109;
}
lean::inc(x_136);
if (lean::is_scalar(x_139)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_139;
}
lean::cnstr_set(x_141, 0, x_136);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_138);
x_142 = x_141;
x_36 = x_142;
x_37 = x_136;
x_38 = x_138;
goto lbl_39;
}
}
}
else
{
obj* x_145; obj* x_147; 
lean::dec(x_0);
lean::dec(x_2);
x_145 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_145);
x_147 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_145);
return x_147;
}
lbl_39:
{
if (x_38 == 0)
{
obj* x_149; uint8 x_151; 
lean::dec(x_36);
x_151 = lean::string_iterator_has_next(x_0);
if (x_151 == 0)
{
obj* x_152; obj* x_153; obj* x_154; obj* x_158; 
x_152 = lean::box(0);
x_153 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_154 = l_mjoin___rarg___closed__1;
lean::inc(x_152);
lean::inc(x_154);
lean::inc(x_153);
x_158 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_153, x_154, x_152, x_152, x_0);
x_149 = x_158;
goto lbl_150;
}
else
{
uint32 x_159; uint8 x_160; obj* x_162; obj* x_163; uint8 x_164; 
x_159 = lean::string_iterator_curr(x_0);
x_162 = lean::mk_nat_obj(65u);
x_163 = lean::box_uint32(x_159);
x_164 = lean::nat_dec_le(x_162, x_163);
lean::dec(x_163);
lean::dec(x_162);
if (x_164 == 0)
{
obj* x_167; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_177; 
x_167 = l_char_quote__core(x_159);
x_168 = l_char_has__repr___closed__1;
lean::inc(x_168);
x_170 = lean::string_append(x_168, x_167);
lean::dec(x_167);
x_172 = lean::string_append(x_170, x_168);
x_173 = lean::box(0);
x_174 = l_mjoin___rarg___closed__1;
lean::inc(x_173);
lean::inc(x_174);
x_177 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_172, x_174, x_173, x_173, x_0);
x_149 = x_177;
goto lbl_150;
}
else
{
uint8 x_178; 
x_178 = 1;
x_160 = x_178;
goto lbl_161;
}
lbl_161:
{
obj* x_179; obj* x_180; uint8 x_181; 
x_179 = lean::mk_nat_obj(70u);
x_180 = lean::box_uint32(x_159);
x_181 = lean::nat_dec_le(x_180, x_179);
lean::dec(x_179);
if (x_181 == 0)
{
obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_191; obj* x_194; 
lean::dec(x_180);
x_184 = l_char_quote__core(x_159);
x_185 = l_char_has__repr___closed__1;
lean::inc(x_185);
x_187 = lean::string_append(x_185, x_184);
lean::dec(x_184);
x_189 = lean::string_append(x_187, x_185);
x_190 = lean::box(0);
x_191 = l_mjoin___rarg___closed__1;
lean::inc(x_190);
lean::inc(x_191);
x_194 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_189, x_191, x_190, x_190, x_0);
x_149 = x_194;
goto lbl_150;
}
else
{
if (x_160 == 0)
{
obj* x_196; obj* x_197; obj* x_199; obj* x_201; obj* x_202; obj* x_203; obj* x_206; 
lean::dec(x_180);
x_196 = l_char_quote__core(x_159);
x_197 = l_char_has__repr___closed__1;
lean::inc(x_197);
x_199 = lean::string_append(x_197, x_196);
lean::dec(x_196);
x_201 = lean::string_append(x_199, x_197);
x_202 = lean::box(0);
x_203 = l_mjoin___rarg___closed__1;
lean::inc(x_202);
lean::inc(x_203);
x_206 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_201, x_203, x_202, x_202, x_0);
x_149 = x_206;
goto lbl_150;
}
else
{
obj* x_207; obj* x_208; obj* x_209; 
x_207 = lean::string_iterator_next(x_0);
x_208 = lean::box(0);
x_209 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_209, 0, x_180);
lean::cnstr_set(x_209, 1, x_207);
lean::cnstr_set(x_209, 2, x_208);
x_149 = x_209;
goto lbl_150;
}
}
}
}
lbl_150:
{
obj* x_210; obj* x_212; 
x_210 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_210, x_149);
if (lean::obj_tag(x_212) == 0)
{
obj* x_213; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_221; obj* x_224; obj* x_225; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_235; 
x_213 = lean::cnstr_get(x_212, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_212, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 2);
lean::inc(x_217);
if (lean::is_shared(x_212)) {
 lean::dec(x_212);
 x_219 = lean::box(0);
} else {
 lean::cnstr_release(x_212, 0);
 lean::cnstr_release(x_212, 1);
 lean::cnstr_release(x_212, 2);
 x_219 = x_212;
}
x_220 = lean::mk_nat_obj(65u);
x_221 = lean::nat_sub(x_213, x_220);
lean::dec(x_220);
lean::dec(x_213);
x_224 = lean::mk_nat_obj(10u);
x_225 = lean::nat_add(x_224, x_221);
lean::dec(x_221);
lean::dec(x_224);
lean::inc(x_210);
if (lean::is_scalar(x_219)) {
 x_229 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_229 = x_219;
}
lean::cnstr_set(x_229, 0, x_225);
lean::cnstr_set(x_229, 1, x_215);
lean::cnstr_set(x_229, 2, x_210);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_217, x_229);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_231);
x_233 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_233);
x_235 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_232, x_233);
return x_235;
}
else
{
obj* x_236; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_246; 
x_236 = lean::cnstr_get(x_212, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_212, sizeof(void*)*1);
if (lean::is_shared(x_212)) {
 lean::dec(x_212);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_212, 0);
 x_239 = x_212;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_236);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_238);
x_241 = x_240;
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_241);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_242);
x_244 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_244);
x_246 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_243, x_244);
return x_246;
}
}
}
else
{
obj* x_249; obj* x_250; obj* x_252; 
lean::dec(x_0);
lean::dec(x_37);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_36);
x_250 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2___closed__1;
lean::inc(x_250);
x_252 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_249, x_250);
return x_252;
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
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_9; obj* x_12; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
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
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_33 = lean::cnstr_get(x_9, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_35 == 0)
{
obj* x_42; 
lean::dec(x_9);
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
lean::inc(x_6);
x_55 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_53, x_45);
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
obj* x_62; uint8 x_64; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
x_36 = x_56;
x_37 = x_62;
x_38 = x_64;
goto lbl_39;
}
}
else
{
obj* x_65; uint8 x_67; obj* x_68; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_42, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
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
obj* x_77; obj* x_78; uint8 x_79; 
if (x_38 == 0)
{
obj* x_83; 
lean::dec(x_36);
lean::inc(x_2);
x_83 = l_lean_parser_monad__parsec_digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__4(x_2);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_88; uint32 x_91; obj* x_94; obj* x_96; obj* x_97; 
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
x_96 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_94, x_86);
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
obj* x_104; uint8 x_106; 
x_104 = lean::cnstr_get(x_97, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
x_77 = x_97;
x_78 = x_104;
x_79 = x_106;
goto lbl_80;
}
}
else
{
obj* x_107; uint8 x_109; obj* x_110; obj* x_112; obj* x_113; 
x_107 = lean::cnstr_get(x_83, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
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
obj* x_120; obj* x_121; uint8 x_122; 
if (x_79 == 0)
{
obj* x_125; obj* x_126; obj* x_130; 
lean::dec(x_77);
x_125 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__3;
x_126 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__3;
lean::inc(x_2);
lean::inc(x_126);
lean::inc(x_125);
x_130 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_125, x_126, x_2);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; obj* x_133; obj* x_136; uint32 x_137; obj* x_140; obj* x_142; obj* x_143; 
x_131 = lean::cnstr_get(x_130, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_130, 2);
lean::inc(x_133);
lean::dec(x_130);
x_136 = lean::mk_nat_obj(95u);
x_137 = lean::unbox_uint32(x_136);
lean::dec(x_136);
lean::inc(x_1);
x_140 = lean::string_push(x_1, x_137);
lean::inc(x_6);
x_142 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_140, x_131);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_142);
if (lean::obj_tag(x_143) == 0)
{
obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_148 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_143);
x_149 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_148);
x_150 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_149);
return x_150;
}
else
{
obj* x_151; uint8 x_153; 
x_151 = lean::cnstr_get(x_143, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get_scalar<uint8>(x_143, sizeof(void*)*1);
x_120 = x_143;
x_121 = x_151;
x_122 = x_153;
goto lbl_123;
}
}
else
{
obj* x_154; uint8 x_156; obj* x_157; obj* x_159; obj* x_160; 
x_154 = lean::cnstr_get(x_130, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get_scalar<uint8>(x_130, sizeof(void*)*1);
if (lean::is_shared(x_130)) {
 lean::dec(x_130);
 x_157 = lean::box(0);
} else {
 lean::cnstr_release(x_130, 0);
 x_157 = x_130;
}
lean::inc(x_154);
if (lean::is_scalar(x_157)) {
 x_159 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_159 = x_157;
}
lean::cnstr_set(x_159, 0, x_154);
lean::cnstr_set_scalar(x_159, sizeof(void*)*1, x_156);
x_160 = x_159;
x_120 = x_160;
x_121 = x_154;
x_122 = x_156;
goto lbl_123;
}
}
else
{
obj* x_166; obj* x_167; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_78);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_77);
x_167 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_166);
return x_167;
}
lbl_123:
{
obj* x_168; obj* x_169; uint8 x_170; 
if (x_122 == 0)
{
obj* x_173; obj* x_174; obj* x_178; 
lean::dec(x_120);
x_173 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_174 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_174);
lean::inc(x_173);
x_178 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_173, x_174, x_2);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_181; obj* x_184; 
x_179 = lean::cnstr_get(x_178, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_178, 2);
lean::inc(x_181);
lean::dec(x_178);
x_184 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_179);
if (lean::obj_tag(x_184) == 0)
{
obj* x_185; obj* x_187; obj* x_189; obj* x_192; 
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 2);
lean::inc(x_189);
lean::dec(x_184);
x_192 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_187);
if (lean::obj_tag(x_192) == 0)
{
obj* x_193; obj* x_195; obj* x_197; obj* x_200; obj* x_201; obj* x_204; obj* x_207; uint8 x_208; 
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 1);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_192, 2);
lean::inc(x_197);
lean::dec(x_192);
x_200 = lean::mk_nat_obj(16u);
x_201 = lean::nat_mul(x_185, x_200);
lean::dec(x_200);
lean::dec(x_185);
x_204 = lean::nat_add(x_201, x_193);
lean::dec(x_193);
lean::dec(x_201);
x_207 = lean::mk_nat_obj(55296u);
x_208 = lean::nat_dec_lt(x_204, x_207);
lean::dec(x_207);
if (x_208 == 0)
{
obj* x_210; uint8 x_211; 
x_210 = lean::mk_nat_obj(57343u);
x_211 = lean::nat_dec_lt(x_210, x_204);
lean::dec(x_210);
if (x_211 == 0)
{
uint32 x_214; obj* x_216; obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_204);
x_214 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_216 = lean::string_push(x_1, x_214);
lean::inc(x_6);
x_218 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_216, x_195);
x_219 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_218);
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_219);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_221);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_226);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_227);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_228);
return x_229;
}
else
{
obj* x_230; uint8 x_232; 
x_230 = lean::cnstr_get(x_221, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
x_168 = x_221;
x_169 = x_230;
x_170 = x_232;
goto lbl_171;
}
}
else
{
obj* x_233; uint8 x_234; 
x_233 = lean::mk_nat_obj(1114112u);
x_234 = lean::nat_dec_lt(x_204, x_233);
lean::dec(x_233);
if (x_234 == 0)
{
uint32 x_237; obj* x_239; obj* x_241; obj* x_242; obj* x_243; obj* x_244; 
lean::dec(x_204);
x_237 = lean::unbox_uint32(x_3);
lean::inc(x_1);
x_239 = lean::string_push(x_1, x_237);
lean::inc(x_6);
x_241 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_239, x_195);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_241);
x_243 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_242);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_243);
if (lean::obj_tag(x_244) == 0)
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_244);
x_250 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_249);
x_251 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_250);
x_252 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_251);
return x_252;
}
else
{
obj* x_253; uint8 x_255; 
x_253 = lean::cnstr_get(x_244, 0);
lean::inc(x_253);
x_255 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
x_168 = x_244;
x_169 = x_253;
x_170 = x_255;
goto lbl_171;
}
}
else
{
uint32 x_256; obj* x_259; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
x_256 = lean::unbox_uint32(x_204);
lean::dec(x_204);
lean::inc(x_1);
x_259 = lean::string_push(x_1, x_256);
lean::inc(x_6);
x_261 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_259, x_195);
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_261);
x_263 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_262);
x_264 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_263);
if (lean::obj_tag(x_264) == 0)
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_269 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_264);
x_270 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_269);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_270);
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_271);
return x_272;
}
else
{
obj* x_273; uint8 x_275; 
x_273 = lean::cnstr_get(x_264, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get_scalar<uint8>(x_264, sizeof(void*)*1);
x_168 = x_264;
x_169 = x_273;
x_170 = x_275;
goto lbl_171;
}
}
}
}
else
{
uint32 x_276; obj* x_279; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_276 = lean::unbox_uint32(x_204);
lean::dec(x_204);
lean::inc(x_1);
x_279 = lean::string_push(x_1, x_276);
lean::inc(x_6);
x_281 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_279, x_195);
x_282 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_281);
x_283 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_282);
x_284 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_283);
if (lean::obj_tag(x_284) == 0)
{
obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_284);
x_290 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_289);
x_291 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_290);
x_292 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_291);
return x_292;
}
else
{
obj* x_293; uint8 x_295; 
x_293 = lean::cnstr_get(x_284, 0);
lean::inc(x_293);
x_295 = lean::cnstr_get_scalar<uint8>(x_284, sizeof(void*)*1);
x_168 = x_284;
x_169 = x_293;
x_170 = x_295;
goto lbl_171;
}
}
}
else
{
obj* x_297; uint8 x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
lean::dec(x_185);
x_297 = lean::cnstr_get(x_192, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*1);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 x_300 = x_192;
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set_scalar(x_301, sizeof(void*)*1, x_299);
x_302 = x_301;
x_303 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_302);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_303);
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
obj* x_313; uint8 x_315; 
x_313 = lean::cnstr_get(x_304, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get_scalar<uint8>(x_304, sizeof(void*)*1);
x_168 = x_304;
x_169 = x_313;
x_170 = x_315;
goto lbl_171;
}
}
}
else
{
obj* x_316; uint8 x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
x_316 = lean::cnstr_get(x_184, 0);
lean::inc(x_316);
x_318 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_319 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_319 = x_184;
}
if (lean::is_scalar(x_319)) {
 x_320 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_320 = x_319;
}
lean::cnstr_set(x_320, 0, x_316);
lean::cnstr_set_scalar(x_320, sizeof(void*)*1, x_318);
x_321 = x_320;
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_321);
if (lean::obj_tag(x_322) == 0)
{
obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_322);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_327);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_328);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_329);
return x_330;
}
else
{
obj* x_331; uint8 x_333; 
x_331 = lean::cnstr_get(x_322, 0);
lean::inc(x_331);
x_333 = lean::cnstr_get_scalar<uint8>(x_322, sizeof(void*)*1);
x_168 = x_322;
x_169 = x_331;
x_170 = x_333;
goto lbl_171;
}
}
}
else
{
obj* x_334; uint8 x_336; obj* x_337; obj* x_339; obj* x_340; 
x_334 = lean::cnstr_get(x_178, 0);
lean::inc(x_334);
x_336 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
if (lean::is_shared(x_178)) {
 lean::dec(x_178);
 x_337 = lean::box(0);
} else {
 lean::cnstr_release(x_178, 0);
 x_337 = x_178;
}
lean::inc(x_334);
if (lean::is_scalar(x_337)) {
 x_339 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_339 = x_337;
}
lean::cnstr_set(x_339, 0, x_334);
lean::cnstr_set_scalar(x_339, sizeof(void*)*1, x_336);
x_340 = x_339;
x_168 = x_340;
x_169 = x_334;
x_170 = x_336;
goto lbl_171;
}
}
else
{
obj* x_346; obj* x_347; obj* x_348; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_121);
x_346 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_120);
x_347 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_346);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_347);
return x_348;
}
lbl_171:
{
if (x_170 == 0)
{
obj* x_350; obj* x_351; obj* x_354; 
lean::dec(x_168);
x_350 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__1;
x_351 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___closed__1;
lean::inc(x_351);
lean::inc(x_350);
x_354 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_350, x_351, x_2);
if (lean::obj_tag(x_354) == 0)
{
obj* x_355; obj* x_357; obj* x_360; 
x_355 = lean::cnstr_get(x_354, 1);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_354, 2);
lean::inc(x_357);
lean::dec(x_354);
x_360 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_355);
if (lean::obj_tag(x_360) == 0)
{
obj* x_361; obj* x_363; obj* x_365; obj* x_368; 
x_361 = lean::cnstr_get(x_360, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_360, 2);
lean::inc(x_365);
lean::dec(x_360);
x_368 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_363);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_371; obj* x_373; obj* x_376; 
x_369 = lean::cnstr_get(x_368, 0);
lean::inc(x_369);
x_371 = lean::cnstr_get(x_368, 1);
lean::inc(x_371);
x_373 = lean::cnstr_get(x_368, 2);
lean::inc(x_373);
lean::dec(x_368);
x_376 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_371);
if (lean::obj_tag(x_376) == 0)
{
obj* x_377; obj* x_379; obj* x_381; obj* x_384; 
x_377 = lean::cnstr_get(x_376, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_376, 1);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_376, 2);
lean::inc(x_381);
lean::dec(x_376);
x_384 = l_lean_parser_parse__hex__digit___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__2(x_379);
if (lean::obj_tag(x_384) == 0)
{
obj* x_385; obj* x_387; obj* x_389; obj* x_392; obj* x_393; obj* x_396; obj* x_397; obj* x_400; obj* x_403; obj* x_404; obj* x_407; obj* x_410; obj* x_413; uint8 x_414; 
x_385 = lean::cnstr_get(x_384, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_384, 1);
lean::inc(x_387);
x_389 = lean::cnstr_get(x_384, 2);
lean::inc(x_389);
lean::dec(x_384);
x_392 = lean::mk_nat_obj(4096u);
x_393 = lean::nat_mul(x_361, x_392);
lean::dec(x_392);
lean::dec(x_361);
x_396 = lean::mk_nat_obj(256u);
x_397 = lean::nat_mul(x_369, x_396);
lean::dec(x_396);
lean::dec(x_369);
x_400 = lean::nat_add(x_393, x_397);
lean::dec(x_397);
lean::dec(x_393);
x_403 = lean::mk_nat_obj(16u);
x_404 = lean::nat_mul(x_377, x_403);
lean::dec(x_403);
lean::dec(x_377);
x_407 = lean::nat_add(x_400, x_404);
lean::dec(x_404);
lean::dec(x_400);
x_410 = lean::nat_add(x_407, x_385);
lean::dec(x_385);
lean::dec(x_407);
x_413 = lean::mk_nat_obj(55296u);
x_414 = lean::nat_dec_lt(x_410, x_413);
lean::dec(x_413);
if (x_414 == 0)
{
obj* x_416; uint8 x_417; 
x_416 = lean::mk_nat_obj(57343u);
x_417 = lean::nat_dec_lt(x_416, x_410);
lean::dec(x_416);
if (x_417 == 0)
{
uint32 x_420; obj* x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; 
lean::dec(x_410);
x_420 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_422 = lean::string_push(x_1, x_420);
x_423 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_422, x_387);
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_389, x_423);
x_425 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_424);
x_426 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_425);
x_427 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_426);
x_428 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_427);
x_429 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_428);
x_430 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_429);
x_431 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_430);
x_432 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_431);
x_433 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_432);
return x_433;
}
else
{
obj* x_434; uint8 x_435; 
x_434 = lean::mk_nat_obj(1114112u);
x_435 = lean::nat_dec_lt(x_410, x_434);
lean::dec(x_434);
if (x_435 == 0)
{
uint32 x_438; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; 
lean::dec(x_410);
x_438 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_440 = lean::string_push(x_1, x_438);
x_441 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_440, x_387);
x_442 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_389, x_441);
x_443 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_442);
x_444 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_443);
x_445 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_444);
x_446 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_445);
x_447 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_446);
x_448 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_447);
x_449 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_448);
x_450 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_449);
x_451 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_450);
return x_451;
}
else
{
uint32 x_453; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; 
lean::dec(x_3);
x_453 = lean::unbox_uint32(x_410);
lean::dec(x_410);
x_455 = lean::string_push(x_1, x_453);
x_456 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_455, x_387);
x_457 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_389, x_456);
x_458 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_457);
x_459 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_458);
x_460 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_459);
x_461 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_460);
x_462 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_461);
x_463 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_462);
x_464 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_463);
x_465 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_464);
x_466 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_465);
return x_466;
}
}
}
else
{
uint32 x_468; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; 
lean::dec(x_3);
x_468 = lean::unbox_uint32(x_410);
lean::dec(x_410);
x_470 = lean::string_push(x_1, x_468);
x_471 = l___private_init_lean_name__mangling_2__parse__mangled__string__aux___main(x_6, x_470, x_387);
x_472 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_389, x_471);
x_473 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_472);
x_474 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_473);
x_475 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_474);
x_476 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_475);
x_477 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_476);
x_478 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_477);
x_479 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_478);
x_480 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_479);
x_481 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_480);
return x_481;
}
}
else
{
obj* x_488; uint8 x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_369);
lean::dec(x_361);
lean::dec(x_377);
x_488 = lean::cnstr_get(x_384, 0);
lean::inc(x_488);
x_490 = lean::cnstr_get_scalar<uint8>(x_384, sizeof(void*)*1);
if (lean::is_shared(x_384)) {
 lean::dec(x_384);
 x_491 = lean::box(0);
} else {
 lean::cnstr_release(x_384, 0);
 x_491 = x_384;
}
if (lean::is_scalar(x_491)) {
 x_492 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_492 = x_491;
}
lean::cnstr_set(x_492, 0, x_488);
lean::cnstr_set_scalar(x_492, sizeof(void*)*1, x_490);
x_493 = x_492;
x_494 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_493);
x_495 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_494);
x_496 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_495);
x_497 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_496);
x_498 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_497);
x_499 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_498);
x_500 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_499);
x_501 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_500);
x_502 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_501);
return x_502;
}
}
else
{
obj* x_508; uint8 x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_369);
lean::dec(x_361);
x_508 = lean::cnstr_get(x_376, 0);
lean::inc(x_508);
x_510 = lean::cnstr_get_scalar<uint8>(x_376, sizeof(void*)*1);
if (lean::is_shared(x_376)) {
 lean::dec(x_376);
 x_511 = lean::box(0);
} else {
 lean::cnstr_release(x_376, 0);
 x_511 = x_376;
}
if (lean::is_scalar(x_511)) {
 x_512 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_512 = x_511;
}
lean::cnstr_set(x_512, 0, x_508);
lean::cnstr_set_scalar(x_512, sizeof(void*)*1, x_510);
x_513 = x_512;
x_514 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_373, x_513);
x_515 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_514);
x_516 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_515);
x_517 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_516);
x_518 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_517);
x_519 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_518);
x_520 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_519);
x_521 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_520);
return x_521;
}
}
else
{
obj* x_526; uint8 x_528; obj* x_529; obj* x_530; obj* x_531; obj* x_532; obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_361);
x_526 = lean::cnstr_get(x_368, 0);
lean::inc(x_526);
x_528 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*1);
if (lean::is_shared(x_368)) {
 lean::dec(x_368);
 x_529 = lean::box(0);
} else {
 lean::cnstr_release(x_368, 0);
 x_529 = x_368;
}
if (lean::is_scalar(x_529)) {
 x_530 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_530 = x_529;
}
lean::cnstr_set(x_530, 0, x_526);
lean::cnstr_set_scalar(x_530, sizeof(void*)*1, x_528);
x_531 = x_530;
x_532 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_531);
x_533 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_532);
x_534 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_533);
x_535 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_534);
x_536 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_535);
x_537 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_536);
x_538 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_537);
return x_538;
}
}
else
{
obj* x_542; uint8 x_544; obj* x_545; obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_542 = lean::cnstr_get(x_360, 0);
lean::inc(x_542);
x_544 = lean::cnstr_get_scalar<uint8>(x_360, sizeof(void*)*1);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_545 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 x_545 = x_360;
}
if (lean::is_scalar(x_545)) {
 x_546 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_546 = x_545;
}
lean::cnstr_set(x_546, 0, x_542);
lean::cnstr_set_scalar(x_546, sizeof(void*)*1, x_544);
x_547 = x_546;
x_548 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_547);
x_549 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_548);
x_550 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_549);
x_551 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_550);
x_552 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_551);
x_553 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_552);
return x_553;
}
}
else
{
obj* x_557; uint8 x_559; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_557 = lean::cnstr_get(x_354, 0);
lean::inc(x_557);
x_559 = lean::cnstr_get_scalar<uint8>(x_354, sizeof(void*)*1);
if (lean::is_shared(x_354)) {
 lean::dec(x_354);
 x_560 = lean::box(0);
} else {
 lean::cnstr_release(x_354, 0);
 x_560 = x_354;
}
if (lean::is_scalar(x_560)) {
 x_561 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_561 = x_560;
}
lean::cnstr_set(x_561, 0, x_557);
lean::cnstr_set_scalar(x_561, sizeof(void*)*1, x_559);
x_562 = x_561;
x_563 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_169, x_562);
x_564 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_563);
x_565 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_564);
x_566 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_565);
x_567 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_566);
return x_567;
}
}
else
{
obj* x_573; obj* x_574; obj* x_575; obj* x_576; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_169);
x_573 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_121, x_168);
x_574 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_78, x_573);
x_575 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_574);
x_576 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_575);
return x_576;
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
obj* x_579; obj* x_581; 
lean::dec(x_3);
lean::dec(x_0);
x_579 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_579);
x_581 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_581, 0, x_1);
lean::cnstr_set(x_581, 1, x_2);
lean::cnstr_set(x_581, 2, x_579);
return x_581;
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
uint32 x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::string_iterator_curr(x_1);
x_14 = lean::box_uint32(x_13);
x_15 = lean::box_uint32(x_0);
x_16 = lean::nat_dec_eq(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_14);
x_19 = l_char_quote__core(x_13);
x_20 = l_char_has__repr___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_24, x_26, x_25, x_25, x_1);
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_29);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::string_iterator_next(x_1);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_14);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
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
obj* x_41; obj* x_42; obj* x_46; 
lean::dec(x_10);
x_41 = l___private_init_lean_name__mangling_4__name_mangle__aux___main___closed__1;
x_42 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___closed__1;
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_41);
x_46 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__1(x_41, x_42, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; obj* x_52; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 2);
lean::inc(x_49);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 lean::cnstr_release(x_46, 2);
 x_51 = x_46;
}
x_52 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_47);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; obj* x_60; uint32 x_61; obj* x_63; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_60 = lean::mk_nat_obj(95u);
x_61 = lean::unbox_uint32(x_60);
lean::dec(x_60);
x_63 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_61, x_55);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_69; 
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 2);
lean::inc(x_66);
lean::dec(x_63);
x_69 = l_lean_parser_monad__parsec_take___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__10(x_53, x_64);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_77; obj* x_78; obj* x_80; obj* x_81; 
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 2);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_lean_string_demangle(x_70);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_78);
if (lean::is_scalar(x_51)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_51;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_72);
lean::cnstr_set(x_80, 2, x_78);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_82; obj* x_84; obj* x_86; 
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_81, 2);
lean::inc(x_86);
lean::dec(x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_82);
x_90 = l_match__failed___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__11(x_84);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_98; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_98 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_94);
return x_98;
}
else
{
obj* x_99; uint8 x_101; 
x_99 = lean::cnstr_get(x_94, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
x_36 = x_94;
x_37 = x_99;
x_38 = x_101;
goto lbl_39;
}
}
else
{
obj* x_102; obj* x_106; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_102 = lean::cnstr_get(x_82, 0);
lean::inc(x_102);
lean::dec(x_82);
lean::inc(x_1);
x_106 = lean_name_mk_string(x_1, x_102);
lean::inc(x_7);
x_108 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_106, x_84);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_111);
if (lean::obj_tag(x_112) == 0)
{
obj* x_116; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_116 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_112);
return x_116;
}
else
{
obj* x_117; uint8 x_119; 
x_117 = lean::cnstr_get(x_112, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
x_36 = x_112;
x_37 = x_117;
x_38 = x_119;
goto lbl_39;
}
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_120 = lean::cnstr_get(x_81, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get_scalar<uint8>(x_81, sizeof(void*)*1);
if (lean::is_shared(x_81)) {
 lean::dec(x_81);
 x_123 = lean::box(0);
} else {
 lean::cnstr_release(x_81, 0);
 x_123 = x_81;
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_122);
x_125 = x_124;
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_132; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_128);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_128, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_128, sizeof(void*)*1);
x_36 = x_128;
x_37 = x_133;
x_38 = x_135;
goto lbl_39;
}
}
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_51);
x_137 = lean::cnstr_get(x_69, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_140 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_140 = x_69;
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_139);
x_142 = x_141;
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_142);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_149; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_149 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_145);
return x_149;
}
else
{
obj* x_150; uint8 x_152; 
x_150 = lean::cnstr_get(x_145, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get_scalar<uint8>(x_145, sizeof(void*)*1);
x_36 = x_145;
x_37 = x_150;
x_38 = x_152;
goto lbl_39;
}
}
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_53);
lean::dec(x_51);
x_155 = lean::cnstr_get(x_63, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_158 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_158 = x_63;
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_155);
lean::cnstr_set_scalar(x_159, sizeof(void*)*1, x_157);
x_160 = x_159;
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_160);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_161);
if (lean::obj_tag(x_162) == 0)
{
obj* x_166; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_162);
return x_166;
}
else
{
obj* x_167; uint8 x_169; 
x_167 = lean::cnstr_get(x_162, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
x_36 = x_162;
x_37 = x_167;
x_38 = x_169;
goto lbl_39;
}
}
}
else
{
obj* x_171; uint8 x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_51);
x_171 = lean::cnstr_get(x_52, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_174 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_174 = x_52;
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_171);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_173);
x_176 = x_175;
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_176);
if (lean::obj_tag(x_177) == 0)
{
obj* x_181; 
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_181 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_177);
return x_181;
}
else
{
obj* x_182; uint8 x_184; 
x_182 = lean::cnstr_get(x_177, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*1);
x_36 = x_177;
x_37 = x_182;
x_38 = x_184;
goto lbl_39;
}
}
}
else
{
obj* x_185; uint8 x_187; obj* x_188; obj* x_190; obj* x_191; 
x_185 = lean::cnstr_get(x_46, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_188 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_188 = x_46;
}
lean::inc(x_185);
if (lean::is_scalar(x_188)) {
 x_190 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_190 = x_188;
}
lean::cnstr_set(x_190, 0, x_185);
lean::cnstr_set_scalar(x_190, sizeof(void*)*1, x_187);
x_191 = x_190;
x_36 = x_191;
x_37 = x_185;
x_38 = x_187;
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
if (x_38 == 0)
{
obj* x_197; uint32 x_198; obj* x_200; 
lean::dec(x_36);
x_197 = lean::mk_nat_obj(95u);
x_198 = lean::unbox_uint32(x_197);
lean::dec(x_197);
x_200 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_198, x_2);
if (lean::obj_tag(x_200) == 0)
{
obj* x_201; obj* x_203; obj* x_206; 
x_201 = lean::cnstr_get(x_200, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_200, 2);
lean::inc(x_203);
lean::dec(x_200);
x_206 = l_lean_parser_monad__parsec_num___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__2(x_201);
if (lean::obj_tag(x_206) == 0)
{
obj* x_207; obj* x_209; obj* x_211; obj* x_214; 
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_206, 2);
lean::inc(x_211);
lean::dec(x_206);
x_214 = l_lean_parser_monad__parsec_ch___at___private_init_lean_name__mangling_5__parse__mangled__name__aux___main___spec__1(x_198, x_209);
if (lean::obj_tag(x_214) == 0)
{
obj* x_215; obj* x_217; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_215 = lean::cnstr_get(x_214, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 2);
lean::inc(x_217);
lean::dec(x_214);
x_220 = lean_name_mk_numeral(x_1, x_207);
x_221 = l___private_init_lean_name__mangling_5__parse__mangled__name__aux___main(x_7, x_220, x_215);
x_222 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_217, x_221);
x_223 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_211, x_222);
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_223);
x_225 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_224);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_225);
return x_226;
}
else
{
obj* x_230; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_207);
lean::dec(x_1);
lean::dec(x_7);
x_230 = lean::cnstr_get(x_214, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get_scalar<uint8>(x_214, sizeof(void*)*1);
if (lean::is_shared(x_214)) {
 lean::dec(x_214);
 x_233 = lean::box(0);
} else {
 lean::cnstr_release(x_214, 0);
 x_233 = x_214;
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_230);
lean::cnstr_set_scalar(x_234, sizeof(void*)*1, x_232);
x_235 = x_234;
x_236 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_211, x_235);
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_238);
return x_239;
}
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_1);
lean::dec(x_7);
x_242 = lean::cnstr_get(x_206, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get_scalar<uint8>(x_206, sizeof(void*)*1);
if (lean::is_shared(x_206)) {
 lean::dec(x_206);
 x_245 = lean::box(0);
} else {
 lean::cnstr_release(x_206, 0);
 x_245 = x_206;
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_242);
lean::cnstr_set_scalar(x_246, sizeof(void*)*1, x_244);
x_247 = x_246;
x_248 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_247);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_248);
x_250 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_249);
return x_250;
}
}
else
{
obj* x_253; uint8 x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_1);
lean::dec(x_7);
x_253 = lean::cnstr_get(x_200, 0);
lean::inc(x_253);
x_255 = lean::cnstr_get_scalar<uint8>(x_200, sizeof(void*)*1);
if (lean::is_shared(x_200)) {
 lean::dec(x_200);
 x_256 = lean::box(0);
} else {
 lean::cnstr_release(x_200, 0);
 x_256 = x_200;
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_253);
lean::cnstr_set_scalar(x_257, sizeof(void*)*1, x_255);
x_258 = x_257;
x_259 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_258);
x_260 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_259);
return x_260;
}
}
else
{
obj* x_265; 
lean::dec(x_37);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_2);
x_265 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_36);
return x_265;
}
}
}
}
}
else
{
obj* x_267; obj* x_269; 
lean::dec(x_0);
x_267 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_267);
x_269 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_269, 0, x_1);
lean::cnstr_set(x_269, 1, x_2);
lean::cnstr_set(x_269, 2, x_267);
return x_269;
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
