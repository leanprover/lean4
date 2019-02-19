// Lean compiler output
// Module: init.lean.ir.parser
// Imports: init.lean.ir.ir init.lean.parser.parsec init.lean.parser.identifier init.lean.parser.string_literal init.lean.ir.reserved
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
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__2;
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(uint32, obj*);
obj* l_lean_ir_parse__untyped__assignment(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat2int(obj*);
}
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__arg(obj*);
uint8 l_char_is__whitespace(uint32);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_ir_str2abinop;
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(obj*, obj*);
extern uint8 l_true_decidable;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_ir_identifier(obj*);
obj* l_lean_ir_identifier___closed__1;
obj* l_lean_ir_parse__instr___closed__2;
obj* l_lean_ir_parse__literal___closed__2;
obj* l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_parse__unop(obj*);
obj* l_lean_ir_parse__type(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(obj*, obj*);
extern obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(obj*);
obj* l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
extern uint32 l_lean_id__end__escape;
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_symbol___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(obj*, obj*);
obj* l_lean_ir_parse__typed__assignment___closed__1;
obj* l_lean_ir_parse__untyped__assignment___lambda__5___boxed(obj*, obj*, obj*);
obj* l_lean_ir_parse__key2val(obj*);
obj* l_lean_ir_parse__uint16___closed__1;
obj* l_lean_ir_parse__phi___closed__1;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_ir_parse__defconst___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13(uint32, obj*);
obj* l_lean_ir_parse__instr___lambda__3___boxed(obj*, obj*, obj*);
uint8 l_char_is__digit(uint32);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__4;
uint32 l_char_of__nat(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(uint32, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__8(obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_ir_parse__typed__assignment___closed__2;
obj* l_lean_ir_parse__decl(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_ir_parse__untyped__assignment___lambda__3(obj*, uint16, uint16, usize);
obj* l_lean_ir_parse__fnid___closed__1;
obj* l_lean_ir_parse__typed__assignment___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(obj*, obj*);
uint8 l_lean_is__id__end__escape(uint32);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(obj*);
obj* l_lean_ir_symbol(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13___boxed(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_lean_ir_parse__untyped__assignment___closed__1;
obj* l_lean_parser_monad__parsec_any___at_lean_ir_parse__literal___spec__4(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(obj*, obj*);
uint8 l_string_is__empty(obj*);
obj* l_lean_ir_keyword___closed__1;
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11___boxed(obj*, obj*);
obj* l_lean_parser_id__part__escaped___at_lean_ir_identifier___spec__11(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__6(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_parse__instr___lambda__3(obj*, uint16, obj*);
obj* l_lean_ir_parse__assign__binop(obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_parse__var___closed__1;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_ir_parse__defconst(obj*);
obj* l_lean_ir_parse__assignment(obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(uint32, obj*);
obj* l_lean_ir_parse__header___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__6(obj*, obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__3;
namespace lean {
uint16 uint16_of_nat(obj*);
}
obj* l_lean_ir_parse__untyped__assignment___closed__5;
obj* l_lean_ir_parse__typed__assignment___closed__3;
obj* l_lean_ir_str2type;
obj* l_lean_ir_parse__usize(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_ir_parse__literal(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(obj*, obj*, obj*);
obj* l_string_to__nat(obj*);
obj* l_lean_ir_parse__instr___closed__3;
obj* l_lean_ir_parse__typed__assignment(obj*, obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_ir_parse__instr___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(obj*);
extern obj* l_list_repr___main___rarg___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_ir_parse__instr___lambda__4(obj*, obj*, obj*);
obj* l_lean_ir_parse__key2val___rarg(obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_ir_str2unop;
obj* l_lean_ir_parse__typed__assignment___closed__4;
obj* l_lean_ir_parse__instr___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__16(obj*, obj*, obj*);
obj* l_lean_ir_parse__literal___closed__3;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__header___spec__2(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_ir_parse__literal___spec__5(obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__14(obj*, obj*, obj*);
obj* l_lean_ir_parse__block(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_ir_parse__var(obj*);
obj* l_id___rarg(obj*);
obj* l_lean_ir_parse__terminator(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_ir_parse__terminator___closed__2;
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_parse__literal___spec__10(obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__1(obj*, uint8, uint8, obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__header___spec__1(obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_ir_identifier___spec__19(obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__4(obj*, obj*, obj*);
obj* l_lean_ir_parse__fnid(obj*);
extern uint32 l_lean_id__begin__escape;
obj* l_lean_ir_parse__def(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_parse__typed__assignment___closed__6;
obj* l_lean_ir_parse__untyped__assignment___closed__7;
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(obj*);
obj* l_lean_ir_parse__terminator___closed__1;
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(obj*, obj*);
obj* l_lean_ir_parse__instr___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_sep__by1___rarg___lambda__1(obj*, obj*);
obj* l_lean_ir_parse__def___lambda__1(obj*, obj*);
obj* l_lean_ir_parse__blockid___closed__1;
obj* l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17___boxed(obj*, obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__3(obj*, uint8, obj*, usize);
extern obj* l_bool_has__repr___closed__2;
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_identifier___spec__12(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__10(obj*, obj*, obj*);
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_lean_ir_parse__usize___closed__1;
uint8 l_lean_ir_is__reserved__name___main(obj*);
obj* l_lean_ir_str2aunop;
obj* l_lean_parser_monad__parsec_digit___at_lean_ir_parse__literal___spec__8(obj*);
obj* l_lean_parser_id__part___at_lean_ir_identifier___spec__2(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__1(obj*, uint8, obj*, obj*);
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7___boxed(obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
extern obj* l_usize__sz;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__5(obj*);
namespace lean {
obj* int_neg(obj*);
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
obj* l_lean_ir_parse__untyped__assignment___lambda__5(obj*, obj*, uint16);
obj* l_lean_ir_parse__terminator___lambda__1(obj*, obj*);
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__terminator___spec__3(obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
extern obj* l_bool_has__repr___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__18(obj*, obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__6;
obj* l_lean_parser_id__part__default___at_lean_ir_identifier___spec__4(obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(obj*);
obj* l_lean_ir_parse__header(uint8, obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__2(obj*, uint8, uint8, obj*);
uint8 l_lean_is__id__first(uint32);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(obj*);
obj* l_lean_ir_parse__literal___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(uint32, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__terminator___spec__2(obj*);
obj* l_lean_ir_parse__instr(obj*);
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
uint8 l_lean_is__id__begin__escape(uint32);
obj* l_lean_ir_parse__instr___lambda__2(obj*, usize, obj*);
obj* l_lean_ir_parse__def___closed__1;
obj* l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
obj* l_lean_ir_keyword(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(uint32, obj*);
extern obj* l_uint16__sz;
obj* l_lean_ir_parse__typed__assignment___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_ir_parse__blockid(obj*);
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(uint32, obj*);
obj* l_lean_ir_parse__assign__unop(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__uint16___closed__2;
obj* l_lean_ir_parse__untyped__assignment___lambda__2(obj*, obj*, obj*);
obj* l_lean_ir_parse__external(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1(obj*);
obj* l_lean_ir_parse__external___closed__1;
obj* l_lean_ir_parse__key2val___main(obj*);
obj* l_lean_ir_parse__key2val___main___rarg(obj*, obj*, obj*);
obj* l_lean_ir_parse__terminator___closed__3;
obj* l_lean_ir_parse__usize___closed__2;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(obj*);
obj* l_lean_ir_parse__instr___lambda__1(uint8, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_parse__uint16(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1(obj*);
obj* l_lean_ir_parse__phi(obj*);
obj* l_lean_ir_parse__typed__assignment___closed__5;
obj* l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(obj* x_0, uint8 x_1, obj* x_2) {
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
x_7 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__whitespace(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_iterator_next(x_2);
x_16 = 1;
x_0 = x_13;
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_symbol___spec__3(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = 0;
x_3 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(x_1, x_2, x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_symbol___spec__3(x_0);
return x_1;
}
}
obj* l_lean_ir_symbol(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_3 = l_string_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_char_has__repr___closed__1;
x_6 = lean::string_append(x_5, x_0);
x_7 = lean::string_append(x_6, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(x_0, x_4, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_10);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_15);
x_17 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_16, x_8);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_9, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_21 = x_9;
} else {
 lean::inc(x_18);
 lean::dec(x_9);
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
x_24 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_23, x_8);
return x_24;
}
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_lean_ir_keyword___closed__1() {
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
obj* l_lean_ir_keyword(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_3 = l_string_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_char_has__repr___closed__1;
x_6 = lean::string_append(x_5, x_0);
x_7 = lean::string_append(x_6, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(x_0, x_4, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; uint8 x_15; 
x_10 = lean::cnstr_get(x_9, 1);
x_12 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = lean::string_iterator_has_next(x_10);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::box(0);
x_17 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_20);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_25);
x_27 = l_lean_parser_parsec__t_try__mk__res___rarg(x_26);
x_28 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_27, x_8);
return x_28;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; 
x_29 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 x_31 = x_19;
} else {
 lean::inc(x_29);
 lean::dec(x_19);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_29, 3);
lean::inc(x_36);
lean::dec(x_29);
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_32);
lean::cnstr_set(x_39, 1, x_34);
lean::cnstr_set(x_39, 2, x_8);
lean::cnstr_set(x_39, 3, x_36);
x_40 = 0;
if (lean::is_scalar(x_31)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_31;
}
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_40);
x_42 = x_41;
return x_42;
}
}
else
{
uint32 x_43; uint8 x_44; 
x_43 = lean::string_iterator_curr(x_10);
x_44 = l_lean_is__id__rest(x_43);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::box(0);
x_46 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_14)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_14;
}
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_10);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 2);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_49);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_54);
x_56 = l_lean_parser_parsec__t_try__mk__res___rarg(x_55);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_56, x_8);
return x_57;
}
else
{
obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; 
x_58 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 x_60 = x_48;
} else {
 lean::inc(x_58);
 lean::dec(x_48);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_58, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_58, 3);
lean::inc(x_65);
lean::dec(x_58);
x_68 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_68, 0, x_61);
lean::cnstr_set(x_68, 1, x_63);
lean::cnstr_set(x_68, 2, x_8);
lean::cnstr_set(x_68, 3, x_65);
x_69 = 0;
if (lean::is_scalar(x_60)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_60;
}
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_69);
x_71 = x_70;
return x_71;
}
}
else
{
obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_14);
x_73 = l_char_quote__core(x_43);
x_74 = lean::string_append(x_5, x_73);
lean::dec(x_73);
x_76 = lean::string_append(x_74, x_5);
x_77 = lean::box(0);
x_78 = l_mjoin___rarg___closed__1;
x_79 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_76, x_78, x_77, x_77, x_10);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
x_88 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_83);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_88);
x_90 = l_lean_parser_parsec__t_try__mk__res___rarg(x_89);
x_91 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_90, x_8);
return x_91;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_102; uint8 x_103; obj* x_104; obj* x_105; 
x_92 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_94 = x_82;
} else {
 lean::inc(x_92);
 lean::dec(x_82);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_92, 3);
lean::inc(x_99);
lean::dec(x_92);
x_102 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_102, 0, x_95);
lean::cnstr_set(x_102, 1, x_97);
lean::cnstr_set(x_102, 2, x_8);
lean::cnstr_set(x_102, 3, x_99);
x_103 = 0;
if (lean::is_scalar(x_94)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_94;
}
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_103);
x_105 = x_104;
return x_105;
}
}
}
}
else
{
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; 
x_106 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_108 = x_9;
} else {
 lean::inc(x_106);
 lean::dec(x_9);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_106, 1);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_106, 3);
lean::inc(x_113);
lean::dec(x_106);
x_116 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_116, 0, x_109);
lean::cnstr_set(x_116, 1, x_111);
lean::cnstr_set(x_116, 2, x_8);
lean::cnstr_set(x_116, 3, x_113);
x_117 = 0;
if (lean::is_scalar(x_108)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_108;
}
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_117);
x_119 = x_118;
return x_119;
}
}
}
obj* l_lean_ir_parse__key2val___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_0, x_4, x_3, x_3, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
lean::inc(x_2);
x_17 = l_lean_ir_keyword(x_11, x_2);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_17, 1);
x_20 = lean::cnstr_get(x_17, 2);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_set(x_17, 1, lean::box(0));
 lean::cnstr_set(x_17, 2, lean::box(0));
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_18);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_24);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
return x_25;
}
else
{
obj* x_29; uint8 x_31; 
x_29 = lean::cnstr_get(x_25, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_25);
x_33 = l_lean_ir_parse__key2val___main___rarg(x_0, x_8, x_2);
x_34 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_33);
return x_34;
}
else
{
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_29);
return x_25;
}
}
}
else
{
obj* x_40; uint8 x_42; obj* x_43; 
lean::dec(x_13);
x_40 = lean::cnstr_get(x_17, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_43 = x_17;
} else {
 lean::inc(x_40);
 lean::dec(x_17);
 x_43 = lean::box(0);
}
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_43);
x_45 = l_lean_ir_parse__key2val___main___rarg(x_0, x_8, x_2);
x_46 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_45);
return x_46;
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_43)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_43;
}
lean::cnstr_set(x_50, 0, x_40);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_42);
x_51 = x_50;
return x_51;
}
}
}
}
}
obj* l_lean_ir_parse__key2val___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___main___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_ir_parse__key2val___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__key2val___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_parse__key2val(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_lean_ir_str2type() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_0 = lean::mk_string("object");
x_1 = 11;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::mk_string("bool");
x_5 = 0;
x_6 = lean::box(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("byte");
x_9 = 1;
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::mk_string("uint16");
x_13 = 2;
x_14 = lean::box(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_string("uint32");
x_17 = 3;
x_18 = lean::box(x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_string("uint64");
x_21 = 4;
x_22 = lean::box(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::mk_string("usize");
x_25 = 5;
x_26 = lean::box(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("int16");
x_29 = 6;
x_30 = lean::box(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_string("int32");
x_33 = 7;
x_34 = lean::box(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::mk_string("int64");
x_37 = 8;
x_38 = lean::box(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::mk_string("float");
x_41 = 9;
x_42 = lean::box(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::mk_string("double");
x_45 = 10;
x_46 = lean::box(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_43);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_39);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_35);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_31);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_27);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_23);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_19);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_15);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_11);
lean::cnstr_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_7);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_3);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
}
obj* l_lean_ir_parse__type(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("type");
x_2 = l_lean_ir_str2type;
x_3 = l_lean_ir_parse__key2val___main___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_ir_str2aunop() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_0 = lean::mk_string("not");
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::mk_string("neg");
x_5 = 1;
x_6 = lean::box(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("ineg");
x_9 = 2;
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::mk_string("nat2int");
x_13 = 3;
x_14 = lean::box(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_string("is_scalar");
x_17 = 4;
x_18 = lean::box(x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_string("is_shared");
x_21 = 5;
x_22 = lean::box(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::mk_string("is_null");
x_25 = 6;
x_26 = lean::box(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("array_copy");
x_29 = 10;
x_30 = lean::box(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_string("sarray_copy");
x_33 = 11;
x_34 = lean::box(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::mk_string("box");
x_37 = 8;
x_38 = lean::box(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::mk_string("unbox");
x_41 = 9;
x_42 = lean::box(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::mk_string("cast");
x_45 = 7;
x_46 = lean::box(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::mk_string("array_size");
x_49 = 12;
x_50 = lean::box(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::mk_string("sarray_size");
x_53 = 13;
x_54 = lean::box(x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::mk_string("string_len");
x_57 = 14;
x_58 = lean::box(x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::mk_string("succ");
x_61 = 15;
x_62 = lean::box(x_61);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::mk_string("tag");
x_65 = 16;
x_66 = lean::box(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::mk_string("tag_ref");
x_69 = 17;
x_70 = lean::box(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::box(0);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_67);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_63);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_59);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_55);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_51);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_47);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_43);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_39);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_35);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_31);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_27);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_23);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_19);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_15);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_11);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_7);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_3);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
}
obj* l_lean_ir_parse__assign__unop(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("unary operator");
x_2 = l_lean_ir_str2aunop;
x_3 = l_lean_ir_parse__key2val___main___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_ir_str2abinop() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; uint8 x_77; obj* x_78; obj* x_79; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_0 = lean::mk_string("add");
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::mk_string("sub");
x_5 = 1;
x_6 = lean::box(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("mul");
x_9 = 2;
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::mk_string("div");
x_13 = 3;
x_14 = lean::box(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_string("mod");
x_17 = 4;
x_18 = lean::box(x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_string("iadd");
x_21 = 5;
x_22 = lean::box(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::mk_string("isub");
x_25 = 6;
x_26 = lean::box(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("imul");
x_29 = 7;
x_30 = lean::box(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_string("idiv");
x_33 = 8;
x_34 = lean::box(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::mk_string("imod");
x_37 = 9;
x_38 = lean::box(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::mk_string("shl");
x_41 = 10;
x_42 = lean::box(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::mk_string("shr");
x_45 = 11;
x_46 = lean::box(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean::mk_string("and");
x_49 = 12;
x_50 = lean::box(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_50);
x_52 = lean::mk_string("or");
x_53 = 13;
x_54 = lean::box(x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::mk_string("xor");
x_57 = 14;
x_58 = lean::box(x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::mk_string("le");
x_61 = 15;
x_62 = lean::box(x_61);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::mk_string("lt");
x_65 = 16;
x_66 = lean::box(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_66);
x_68 = lean::mk_string("eq");
x_69 = 17;
x_70 = lean::box(x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::mk_string("ne");
x_73 = 18;
x_74 = lean::box(x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::mk_string("ile");
x_77 = 19;
x_78 = lean::box(x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::mk_string("ilt");
x_81 = 20;
x_82 = lean::box(x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_80);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::mk_string("ieq");
x_85 = 21;
x_86 = lean::box(x_85);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::mk_string("ine");
x_89 = 22;
x_90 = lean::box(x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::mk_string("array_read");
x_93 = 23;
x_94 = lean::box(x_93);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::mk_string("array_push");
x_97 = 24;
x_98 = lean::box(x_97);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_98);
x_100 = lean::mk_string("string_push");
x_101 = 25;
x_102 = lean::box(x_101);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_102);
x_104 = lean::mk_string("string_append");
x_105 = 26;
x_106 = lean::box(x_105);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set(x_107, 1, x_106);
x_108 = lean::box(0);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_108);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_103);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_99);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_95);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_91);
lean::cnstr_set(x_113, 1, x_112);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_87);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_83);
lean::cnstr_set(x_115, 1, x_114);
x_116 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_116, 0, x_79);
lean::cnstr_set(x_116, 1, x_115);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_75);
lean::cnstr_set(x_117, 1, x_116);
x_118 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_118, 0, x_71);
lean::cnstr_set(x_118, 1, x_117);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_67);
lean::cnstr_set(x_119, 1, x_118);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_63);
lean::cnstr_set(x_120, 1, x_119);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_59);
lean::cnstr_set(x_121, 1, x_120);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_55);
lean::cnstr_set(x_122, 1, x_121);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_51);
lean::cnstr_set(x_123, 1, x_122);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_47);
lean::cnstr_set(x_124, 1, x_123);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_43);
lean::cnstr_set(x_125, 1, x_124);
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_39);
lean::cnstr_set(x_126, 1, x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_35);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_31);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_27);
lean::cnstr_set(x_129, 1, x_128);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_23);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_19);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_15);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_11);
lean::cnstr_set(x_133, 1, x_132);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_7);
lean::cnstr_set(x_134, 1, x_133);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_3);
lean::cnstr_set(x_135, 1, x_134);
return x_135;
}
}
obj* l_lean_ir_parse__assign__binop(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("binary operator");
x_2 = l_lean_ir_str2abinop;
x_3 = l_lean_ir_parse__key2val___main___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_lean_ir_str2unop() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_0 = lean::mk_string("inc_ref");
x_1 = 0;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::mk_string("dec_ref");
x_5 = 1;
x_6 = lean::box(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("inc");
x_9 = 3;
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::mk_string("dec");
x_13 = 4;
x_14 = lean::box(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_string("dec_sref");
x_17 = 2;
x_18 = lean::box(x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_string("free");
x_21 = 5;
x_22 = lean::box(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::mk_string("dealloc");
x_25 = 6;
x_26 = lean::box(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("array_pop");
x_29 = 7;
x_30 = lean::box(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_string("sarray_pop");
x_33 = 8;
x_34 = lean::box(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_31);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_27);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_23);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_19);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_15);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_11);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_7);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_3);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
obj* l_lean_ir_parse__unop(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("unary operator");
x_2 = l_lean_ir_str2unop;
x_3 = l_lean_ir_parse__key2val___main___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(uint32 x_0, obj* x_1) {
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
x_6 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_4, x_5, x_3, x_3, x_1);
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
x_18 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_15, x_17, x_16, x_16, x_1);
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
obj* l_lean_parser_monad__parsec_any___at_lean_ir_parse__literal___spec__4(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_5);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_0);
x_9 = l_true_decidable;
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
x_17 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_14, x_16, x_15, x_15, x_0);
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
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
x_4 = lean::box(0);
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_0, x_5, x_3, x_4, x_2);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_ir_parse__literal___spec__8(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_17 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_14, x_16, x_15, x_15, x_0);
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
obj* _init_l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at_lean_ir_parse__literal___spec__8(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
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
x_23 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
 lean::cnstr_set(x_6, 0, lean::box(0));
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
x_47 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_44, x_45, x_43, x_43, x_0);
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
x_61 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_57, x_59, x_58, x_58, x_0);
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
x_73 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_69, x_71, x_70, x_70, x_0);
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
x_82 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_78, x_80, x_79, x_79, x_0);
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
 lean::cnstr_set(x_89, 0, lean::box(0));
 lean::cnstr_set(x_89, 1, lean::box(0));
 lean::cnstr_set(x_89, 2, lean::box(0));
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
x_109 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
 lean::cnstr_set(x_89, 0, lean::box(0));
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
x_123 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_132 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_130, x_131, x_129, x_129, x_0);
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
x_145 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_142, x_144, x_143, x_143, x_0);
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
x_156 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_153, x_155, x_154, x_154, x_0);
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
x_164 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_161, x_163, x_162, x_162, x_0);
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
 lean::cnstr_set(x_170, 0, lean::box(0));
 lean::cnstr_set(x_170, 1, lean::box(0));
 lean::cnstr_set(x_170, 2, lean::box(0));
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
x_190 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
x_191 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_189, x_190);
return x_191;
}
else
{
obj* x_192; uint8 x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_192 = lean::cnstr_get(x_170, 0);
x_194 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_exclusive(x_170)) {
 lean::cnstr_set(x_170, 0, lean::box(0));
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
x_200 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_205 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
x_206 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_204, x_205);
return x_206;
}
}
}
}
}
obj* l_lean_parser_parse__quoted__char___at_lean_ir_parse__literal___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_any___at_lean_ir_parse__literal___spec__4(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; uint32 x_16; uint32 x_17; uint8 x_18; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_16 = 92;
x_17 = lean::unbox_uint32(x_3);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
obj* x_19; 
x_19 = lean::box(0);
x_14 = x_19;
goto lbl_15;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_9);
lean::dec(x_0);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_23 = lean::box_uint32(x_16);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_22);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_25);
return x_26;
}
lbl_11:
{
uint32 x_28; uint32 x_29; uint8 x_30; 
lean::dec(x_10);
x_28 = 117;
x_29 = lean::unbox_uint32(x_3);
x_30 = x_29 == x_28;
if (x_30 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_9);
x_32 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
x_33 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_32, x_0, x_5);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_33);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_34);
return x_36;
}
else
{
obj* x_38; 
lean::dec(x_0);
x_38 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_5);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_43; obj* x_46; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_46 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_41);
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
x_54 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_49);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_62; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 2);
lean::inc(x_59);
lean::dec(x_54);
x_62 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_57);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_81; obj* x_83; uint32 x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
lean::dec(x_62);
x_70 = lean::mk_nat_obj(16u);
x_71 = lean::nat_mul(x_70, x_39);
lean::dec(x_39);
x_73 = lean::nat_add(x_71, x_47);
lean::dec(x_47);
lean::dec(x_71);
x_76 = lean::nat_mul(x_70, x_73);
lean::dec(x_73);
x_78 = lean::nat_add(x_76, x_55);
lean::dec(x_55);
lean::dec(x_76);
x_81 = lean::nat_mul(x_70, x_78);
lean::dec(x_78);
x_83 = lean::nat_add(x_81, x_63);
lean::dec(x_63);
lean::dec(x_81);
x_86 = l_char_of__nat(x_83);
x_87 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_88 = lean::box_uint32(x_86);
if (lean::is_scalar(x_9)) {
 x_89 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_89 = x_9;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_65);
lean::cnstr_set(x_89, 2, x_87);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_89);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_93);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_94);
return x_95;
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_55);
lean::dec(x_47);
lean::dec(x_39);
lean::dec(x_9);
x_100 = lean::cnstr_get(x_62, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_103 = x_62;
} else {
 lean::inc(x_100);
 lean::dec(x_62);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_108);
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
return x_111;
}
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_47);
lean::dec(x_39);
lean::dec(x_9);
x_115 = lean::cnstr_get(x_54, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_set(x_54, 0, lean::box(0));
 x_118 = x_54;
} else {
 lean::inc(x_115);
 lean::dec(x_54);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_121);
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_122);
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_123);
return x_125;
}
}
else
{
obj* x_128; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_39);
lean::dec(x_9);
x_128 = lean::cnstr_get(x_46, 0);
x_130 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 x_131 = x_46;
} else {
 lean::inc(x_128);
 lean::dec(x_46);
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
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_134);
x_136 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_136, x_135);
return x_137;
}
}
else
{
obj* x_139; uint8 x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_9);
x_139 = lean::cnstr_get(x_38, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 x_142 = x_38;
} else {
 lean::inc(x_139);
 lean::dec(x_38);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_139);
lean::cnstr_set_scalar(x_143, sizeof(void*)*1, x_141);
x_144 = x_143;
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_144);
x_146 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_146, x_145);
return x_147;
}
}
}
lbl_13:
{
uint32 x_149; uint32 x_150; uint8 x_151; 
lean::dec(x_12);
x_149 = 116;
x_150 = lean::unbox_uint32(x_3);
x_151 = x_150 == x_149;
if (x_151 == 0)
{
uint32 x_152; uint8 x_153; 
x_152 = 120;
x_153 = x_150 == x_152;
if (x_153 == 0)
{
obj* x_154; 
x_154 = lean::box(0);
x_10 = x_154;
goto lbl_11;
}
else
{
obj* x_157; 
lean::dec(x_9);
lean::dec(x_0);
x_157 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_5);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_160; obj* x_162; obj* x_164; obj* x_165; 
x_158 = lean::cnstr_get(x_157, 0);
x_160 = lean::cnstr_get(x_157, 1);
x_162 = lean::cnstr_get(x_157, 2);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_set(x_157, 0, lean::box(0));
 lean::cnstr_set(x_157, 1, lean::box(0));
 lean::cnstr_set(x_157, 2, lean::box(0));
 x_164 = x_157;
} else {
 lean::inc(x_158);
 lean::inc(x_160);
 lean::inc(x_162);
 lean::dec(x_157);
 x_164 = lean::box(0);
}
x_165 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_160);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_168; obj* x_170; obj* x_173; obj* x_174; obj* x_176; uint32 x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_165, 1);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_165, 2);
lean::inc(x_170);
lean::dec(x_165);
x_173 = lean::mk_nat_obj(16u);
x_174 = lean::nat_mul(x_173, x_158);
lean::dec(x_158);
x_176 = lean::nat_add(x_174, x_166);
lean::dec(x_166);
lean::dec(x_174);
x_179 = l_char_of__nat(x_176);
x_180 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_181 = lean::box_uint32(x_179);
if (lean::is_scalar(x_164)) {
 x_182 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_182 = x_164;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_168);
lean::cnstr_set(x_182, 2, x_180);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_162, x_183);
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_184);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_180, x_185);
return x_186;
}
else
{
obj* x_189; uint8 x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_158);
lean::dec(x_164);
x_189 = lean::cnstr_get(x_165, 0);
x_191 = lean::cnstr_get_scalar<uint8>(x_165, sizeof(void*)*1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_set(x_165, 0, lean::box(0));
 x_192 = x_165;
} else {
 lean::inc(x_189);
 lean::dec(x_165);
 x_192 = lean::box(0);
}
if (lean::is_scalar(x_192)) {
 x_193 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_193 = x_192;
}
lean::cnstr_set(x_193, 0, x_189);
lean::cnstr_set_scalar(x_193, sizeof(void*)*1, x_191);
x_194 = x_193;
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_162, x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_195);
x_197 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_197, x_196);
return x_198;
}
}
else
{
obj* x_199; uint8 x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_199 = lean::cnstr_get(x_157, 0);
x_201 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_set(x_157, 0, lean::box(0));
 x_202 = x_157;
} else {
 lean::inc(x_199);
 lean::dec(x_157);
 x_202 = lean::box(0);
}
if (lean::is_scalar(x_202)) {
 x_203 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_203 = x_202;
}
lean::cnstr_set(x_203, 0, x_199);
lean::cnstr_set_scalar(x_203, sizeof(void*)*1, x_201);
x_204 = x_203;
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_204);
x_206 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_206, x_205);
return x_207;
}
}
}
else
{
uint32 x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_9);
lean::dec(x_0);
x_210 = 9;
x_211 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_212 = lean::box_uint32(x_210);
x_213 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_213, 0, x_212);
lean::cnstr_set(x_213, 1, x_5);
lean::cnstr_set(x_213, 2, x_211);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_213);
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_211, x_214);
return x_215;
}
}
lbl_15:
{
uint32 x_217; uint32 x_218; uint8 x_219; 
lean::dec(x_14);
x_217 = 34;
x_218 = lean::unbox_uint32(x_3);
x_219 = x_218 == x_217;
if (x_219 == 0)
{
uint32 x_220; uint8 x_221; 
x_220 = 39;
x_221 = x_218 == x_220;
if (x_221 == 0)
{
uint32 x_222; uint8 x_223; 
x_222 = 110;
x_223 = x_218 == x_222;
if (x_223 == 0)
{
obj* x_224; 
x_224 = lean::box(0);
x_12 = x_224;
goto lbl_13;
}
else
{
uint32 x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_9);
lean::dec(x_0);
x_227 = 10;
x_228 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_229 = lean::box_uint32(x_227);
x_230 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_5);
lean::cnstr_set(x_230, 2, x_228);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_230);
x_232 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_228, x_231);
return x_232;
}
}
else
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_9);
lean::dec(x_0);
x_235 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_236 = lean::box_uint32(x_220);
x_237 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_5);
lean::cnstr_set(x_237, 2, x_235);
x_238 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_237);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_235, x_238);
return x_239;
}
}
else
{
obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_9);
lean::dec(x_0);
x_242 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_243 = lean::box_uint32(x_217);
x_244 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_244, 0, x_243);
lean::cnstr_set(x_244, 1, x_5);
lean::cnstr_set(x_244, 2, x_242);
x_245 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_244);
x_246 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_242, x_245);
return x_246;
}
}
}
else
{
obj* x_248; uint8 x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
lean::dec(x_0);
x_248 = lean::cnstr_get(x_2, 0);
x_250 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_251 = x_2;
} else {
 lean::inc(x_248);
 lean::dec(x_2);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_248);
lean::cnstr_set_scalar(x_252, sizeof(void*)*1, x_250);
x_253 = x_252;
x_254 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_255 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_254, x_253);
return x_255;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_any___at_lean_ir_parse__literal___spec__4(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; uint32 x_16; uint32 x_17; uint8 x_18; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_0);
x_16 = 92;
x_17 = lean::unbox_uint32(x_6);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 34;
x_20 = x_17 == x_19;
if (x_20 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_12);
x_22 = lean::string_push(x_1, x_17);
x_23 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_14, x_22, x_8);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_23);
return x_24;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_14);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_8);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_27);
return x_28;
}
}
else
{
obj* x_30; 
lean::dec(x_12);
x_30 = l_lean_parser_parse__quoted__char___at_lean_ir_parse__literal___spec__5(x_8);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_35; uint32 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 2);
lean::inc(x_35);
lean::dec(x_30);
x_38 = lean::unbox_uint32(x_31);
x_39 = lean::string_push(x_1, x_38);
x_40 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_14, x_39, x_33);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_41);
return x_42;
}
else
{
obj* x_45; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_14);
x_45 = lean::cnstr_get(x_30, 0);
x_47 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_set(x_30, 0, lean::box(0));
 x_48 = x_30;
} else {
 lean::inc(x_45);
 lean::dec(x_30);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_47);
x_50 = x_49;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_50);
return x_51;
}
}
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_0);
x_54 = lean::cnstr_get(x_5, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_57 = x_5;
} else {
 lean::inc(x_54);
 lean::dec(x_5);
 x_57 = lean::box(0);
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
uint32 x_61; obj* x_62; 
lean::dec(x_0);
x_61 = 34;
x_62 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_61, x_2);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_63 = lean::cnstr_get(x_62, 1);
x_65 = lean::cnstr_get(x_62, 2);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_set(x_62, 1, lean::box(0));
 lean::cnstr_set(x_62, 2, lean::box(0));
 x_67 = x_62;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_1);
lean::cnstr_set(x_69, 1, x_63);
lean::cnstr_set(x_69, 2, x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_69);
return x_70;
}
else
{
obj* x_72; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_1);
x_72 = lean::cnstr_get(x_62, 0);
x_74 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_set(x_62, 0, lean::box(0));
 x_75 = x_62;
} else {
 lean::inc(x_72);
 lean::dec(x_62);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_74);
x_77 = x_76;
return x_77;
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = 34;
x_2 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::string_iterator_remaining(x_3);
x_9 = l_string_join___closed__1;
x_10 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_8, x_9, x_3);
x_11 = l_lean_ir_keyword___closed__1;
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_10);
x_13 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_12);
return x_13;
}
else
{
obj* x_14; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_17 = x_2;
} else {
 lean::inc(x_14);
 lean::dec(x_2);
 x_17 = lean::box(0);
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
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__12(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__12(x_4, x_3, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__14(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__14(x_4, x_3, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__16(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_2);
x_6 = lean::string_iterator_remaining(x_1);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__16(x_6, x_5, x_1);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_parse__literal___spec__10(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_16 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(x_15, x_10);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
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
x_33 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_30, x_32, x_31, x_31, x_0);
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
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(x_43, x_38);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_44);
return x_45;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_35, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
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
x_55 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(x_0, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_55);
return x_56;
}
}
}
}
obj* l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while1___at_lean_ir_parse__literal___spec__10(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
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
 lean::cnstr_set(x_1, 0, lean::box(0));
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
obj* _init_l_lean_ir_parse__literal___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("numeral");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__literal___closed__2() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::alloc_cnstr(0, 0, 1);
lean::cnstr_set_scalar(x_1, 0, x_0);
x_2 = x_1;
return x_2;
}
}
obj* _init_l_lean_ir_parse__literal___closed__3() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; 
x_0 = 1;
x_1 = lean::alloc_cnstr(0, 0, 1);
lean::cnstr_set_scalar(x_1, 0, x_0);
x_2 = x_1;
return x_2;
}
}
obj* l_lean_ir_parse__literal(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; obj* x_4; obj* x_6; 
x_1 = 45;
x_4 = l_bool_has__repr___closed__2;
lean::inc(x_0);
x_6 = l_lean_ir_keyword(x_4, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_6, 1);
x_9 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_lean_ir_parse__literal___closed__3;
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_14);
x_2 = x_15;
goto lbl_3;
}
else
{
obj* x_16; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 0);
x_18 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_19 = x_6;
} else {
 lean::inc(x_16);
 lean::dec(x_6);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_18);
x_21 = x_20;
x_2 = x_21;
goto lbl_3;
}
lbl_3:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; uint8 x_28; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_25 == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_2);
x_31 = l_bool_has__repr___closed__1;
lean::inc(x_0);
x_33 = l_lean_ir_keyword(x_31, x_0);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_34 = lean::cnstr_get(x_33, 1);
x_36 = lean::cnstr_get(x_33, 2);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_set(x_33, 1, lean::box(0));
 lean::cnstr_set(x_33, 2, lean::box(0));
 x_38 = x_33;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
x_39 = l_lean_ir_parse__literal___closed__2;
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_38)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_38;
}
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_34);
lean::cnstr_set(x_41, 2, x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_41);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; 
lean::dec(x_0);
x_44 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_42);
return x_44;
}
else
{
obj* x_45; uint8 x_47; 
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
x_26 = x_42;
x_27 = x_45;
x_28 = x_47;
goto lbl_29;
}
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_53; obj* x_54; 
x_48 = lean::cnstr_get(x_33, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_51 = x_33;
} else {
 lean::inc(x_48);
 lean::dec(x_33);
 x_51 = lean::box(0);
}
lean::inc(x_48);
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_48);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_50);
x_54 = x_53;
x_26 = x_54;
x_27 = x_48;
x_28 = x_50;
goto lbl_29;
}
}
else
{
lean::dec(x_0);
lean::dec(x_23);
return x_2;
}
lbl_29:
{
obj* x_57; obj* x_58; uint8 x_59; 
if (x_28 == 0)
{
obj* x_63; 
lean::dec(x_26);
lean::inc(x_0);
x_63 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_0);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; 
x_64 = lean::cnstr_get(x_63, 0);
x_66 = lean::cnstr_get(x_63, 1);
x_68 = lean::cnstr_get(x_63, 2);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 lean::cnstr_set(x_63, 2, lean::box(0));
 x_70 = x_63;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_63);
 x_70 = lean::box(0);
}
x_71 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_66);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_72 = lean::cnstr_get(x_71, 1);
x_74 = lean::cnstr_get(x_71, 2);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_set(x_71, 1, lean::box(0));
 lean::cnstr_set(x_71, 2, lean::box(0));
 x_76 = x_71;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_71);
 x_76 = lean::box(0);
}
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_70)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_70;
}
lean::cnstr_set(x_78, 0, x_64);
lean::cnstr_set(x_78, 1, x_72);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_79);
x_81 = l_lean_ir_parse__literal___closed__1;
x_82 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_80, x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 2);
lean::inc(x_87);
lean::dec(x_82);
x_90 = lean::nat2int(x_83);
x_91 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
if (lean::is_scalar(x_76)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_76;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_85);
lean::cnstr_set(x_92, 2, x_77);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_96; 
lean::dec(x_0);
x_95 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_93);
x_96 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_95);
return x_96;
}
else
{
obj* x_97; uint8 x_99; 
x_97 = lean::cnstr_get(x_93, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_93, sizeof(void*)*1);
x_57 = x_93;
x_58 = x_97;
x_59 = x_99;
goto lbl_60;
}
}
else
{
obj* x_101; uint8 x_103; obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_76);
x_101 = lean::cnstr_get(x_82, 0);
x_103 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_set(x_82, 0, lean::box(0));
 x_104 = x_82;
} else {
 lean::inc(x_101);
 lean::dec(x_82);
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
x_57 = x_107;
x_58 = x_101;
x_59 = x_103;
goto lbl_60;
}
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_64);
x_109 = lean::cnstr_get(x_71, 0);
x_111 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 x_112 = x_71;
} else {
 lean::inc(x_109);
 lean::dec(x_71);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_114);
x_116 = l_lean_ir_parse__literal___closed__1;
x_117 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_115, x_116);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_120; obj* x_122; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 2);
lean::inc(x_122);
lean::dec(x_117);
x_125 = lean::nat2int(x_118);
x_126 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
x_127 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_70)) {
 x_128 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_128 = x_70;
}
lean::cnstr_set(x_128, 0, x_126);
lean::cnstr_set(x_128, 1, x_120);
lean::cnstr_set(x_128, 2, x_127);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_131; obj* x_132; 
lean::dec(x_0);
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_129);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_131);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_129, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_129, sizeof(void*)*1);
x_57 = x_129;
x_58 = x_133;
x_59 = x_135;
goto lbl_60;
}
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_142; obj* x_143; 
lean::dec(x_70);
x_137 = lean::cnstr_get(x_117, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_117, sizeof(void*)*1);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_set(x_117, 0, lean::box(0));
 x_140 = x_117;
} else {
 lean::inc(x_137);
 lean::dec(x_117);
 x_140 = lean::box(0);
}
lean::inc(x_137);
if (lean::is_scalar(x_140)) {
 x_142 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_142 = x_140;
}
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set_scalar(x_142, sizeof(void*)*1, x_139);
x_143 = x_142;
x_57 = x_143;
x_58 = x_137;
x_59 = x_139;
goto lbl_60;
}
}
}
else
{
obj* x_144; uint8 x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_144 = lean::cnstr_get(x_63, 0);
x_146 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 x_147 = x_63;
} else {
 lean::inc(x_144);
 lean::dec(x_63);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_144);
lean::cnstr_set_scalar(x_148, sizeof(void*)*1, x_146);
x_149 = x_148;
x_150 = l_lean_ir_parse__literal___closed__1;
x_151 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_149, x_150);
if (lean::obj_tag(x_151) == 0)
{
obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_152 = lean::cnstr_get(x_151, 0);
x_154 = lean::cnstr_get(x_151, 1);
x_156 = lean::cnstr_get(x_151, 2);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_set(x_151, 0, lean::box(0));
 lean::cnstr_set(x_151, 1, lean::box(0));
 lean::cnstr_set(x_151, 2, lean::box(0));
 x_158 = x_151;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::inc(x_156);
 lean::dec(x_151);
 x_158 = lean::box(0);
}
x_159 = lean::nat2int(x_152);
x_160 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_160, 0, x_159);
x_161 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_158)) {
 x_162 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_162 = x_158;
}
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_154);
lean::cnstr_set(x_162, 2, x_161);
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_156, x_162);
if (lean::obj_tag(x_163) == 0)
{
obj* x_165; obj* x_166; 
lean::dec(x_0);
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_163);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_165);
return x_166;
}
else
{
obj* x_167; uint8 x_169; 
x_167 = lean::cnstr_get(x_163, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get_scalar<uint8>(x_163, sizeof(void*)*1);
x_57 = x_163;
x_58 = x_167;
x_59 = x_169;
goto lbl_60;
}
}
else
{
obj* x_170; uint8 x_172; obj* x_173; obj* x_175; obj* x_176; 
x_170 = lean::cnstr_get(x_151, 0);
x_172 = lean::cnstr_get_scalar<uint8>(x_151, sizeof(void*)*1);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_set(x_151, 0, lean::box(0));
 x_173 = x_151;
} else {
 lean::inc(x_170);
 lean::dec(x_151);
 x_173 = lean::box(0);
}
lean::inc(x_170);
if (lean::is_scalar(x_173)) {
 x_175 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_175 = x_173;
}
lean::cnstr_set(x_175, 0, x_170);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_172);
x_176 = x_175;
x_57 = x_176;
x_58 = x_170;
x_59 = x_172;
goto lbl_60;
}
}
}
else
{
obj* x_179; 
lean::dec(x_0);
lean::dec(x_27);
x_179 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_26);
return x_179;
}
lbl_60:
{
obj* x_180; obj* x_181; obj* x_182; obj* x_184; uint8 x_185; 
if (x_59 == 0)
{
obj* x_189; 
lean::dec(x_57);
lean::inc(x_0);
x_189 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_1, x_0);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; obj* x_192; obj* x_194; obj* x_195; 
x_190 = lean::cnstr_get(x_189, 1);
x_192 = lean::cnstr_get(x_189, 2);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_set(x_189, 1, lean::box(0));
 lean::cnstr_set(x_189, 2, lean::box(0));
 x_194 = x_189;
} else {
 lean::inc(x_190);
 lean::inc(x_192);
 lean::dec(x_189);
 x_194 = lean::box(0);
}
x_195 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_190);
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
x_203 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_198);
if (lean::obj_tag(x_203) == 0)
{
obj* x_204; obj* x_206; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
x_204 = lean::cnstr_get(x_203, 1);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 2);
lean::inc(x_206);
lean::dec(x_203);
x_209 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_194)) {
 x_210 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_210 = x_194;
}
lean::cnstr_set(x_210, 0, x_196);
lean::cnstr_set(x_210, 1, x_204);
lean::cnstr_set(x_210, 2, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_206, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_212);
if (lean::obj_tag(x_213) == 0)
{
obj* x_214; obj* x_216; obj* x_218; 
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_213, 1);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_213, 2);
lean::inc(x_218);
lean::dec(x_213);
x_180 = x_214;
x_181 = x_216;
x_182 = x_218;
goto lbl_183;
}
else
{
obj* x_221; uint8 x_223; 
x_221 = lean::cnstr_get(x_213, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get_scalar<uint8>(x_213, sizeof(void*)*1);
lean::dec(x_213);
x_184 = x_221;
x_185 = x_223;
goto lbl_186;
}
}
else
{
obj* x_227; uint8 x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_196);
lean::dec(x_194);
x_227 = lean::cnstr_get(x_203, 0);
x_229 = lean::cnstr_get_scalar<uint8>(x_203, sizeof(void*)*1);
if (lean::is_exclusive(x_203)) {
 lean::cnstr_set(x_203, 0, lean::box(0));
 x_230 = x_203;
} else {
 lean::inc(x_227);
 lean::dec(x_203);
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
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_232);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_233);
if (lean::obj_tag(x_234) == 0)
{
obj* x_235; obj* x_237; obj* x_239; 
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_234, 2);
lean::inc(x_239);
lean::dec(x_234);
x_180 = x_235;
x_181 = x_237;
x_182 = x_239;
goto lbl_183;
}
else
{
obj* x_242; uint8 x_244; 
x_242 = lean::cnstr_get(x_234, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
lean::dec(x_234);
x_184 = x_242;
x_185 = x_244;
goto lbl_186;
}
}
}
else
{
obj* x_247; uint8 x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
lean::dec(x_194);
x_247 = lean::cnstr_get(x_195, 0);
x_249 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_set(x_195, 0, lean::box(0));
 x_250 = x_195;
} else {
 lean::inc(x_247);
 lean::dec(x_195);
 x_250 = lean::box(0);
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_247);
lean::cnstr_set_scalar(x_251, sizeof(void*)*1, x_249);
x_252 = x_251;
x_253 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_252);
if (lean::obj_tag(x_253) == 0)
{
obj* x_254; obj* x_256; obj* x_258; 
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_253, 1);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_253, 2);
lean::inc(x_258);
lean::dec(x_253);
x_180 = x_254;
x_181 = x_256;
x_182 = x_258;
goto lbl_183;
}
else
{
obj* x_261; uint8 x_263; 
x_261 = lean::cnstr_get(x_253, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get_scalar<uint8>(x_253, sizeof(void*)*1);
lean::dec(x_253);
x_184 = x_261;
x_185 = x_263;
goto lbl_186;
}
}
}
else
{
obj* x_265; uint8 x_267; 
x_265 = lean::cnstr_get(x_189, 0);
lean::inc(x_265);
x_267 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*1);
lean::dec(x_189);
x_184 = x_265;
x_185 = x_267;
goto lbl_186;
}
}
else
{
obj* x_271; obj* x_272; 
lean::dec(x_58);
lean::dec(x_0);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_57);
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_271);
return x_272;
}
lbl_183:
{
obj* x_273; obj* x_274; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
x_273 = lean::nat2int(x_180);
x_274 = lean::int_neg(x_273);
lean::dec(x_273);
x_276 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_276, 0, x_274);
x_277 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_278 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_278, 0, x_276);
lean::cnstr_set(x_278, 1, x_181);
lean::cnstr_set(x_278, 2, x_277);
x_279 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_278);
if (lean::obj_tag(x_279) == 0)
{
obj* x_281; obj* x_282; obj* x_283; 
lean::dec(x_0);
x_281 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_279);
x_282 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_281);
x_283 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_282);
return x_283;
}
else
{
obj* x_284; uint8 x_286; 
x_284 = lean::cnstr_get(x_279, 0);
lean::inc(x_284);
x_286 = lean::cnstr_get_scalar<uint8>(x_279, sizeof(void*)*1);
if (x_286 == 0)
{
obj* x_288; 
lean::dec(x_279);
x_288 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_288) == 0)
{
obj* x_289; obj* x_291; obj* x_293; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
x_289 = lean::cnstr_get(x_288, 0);
x_291 = lean::cnstr_get(x_288, 1);
x_293 = lean::cnstr_get(x_288, 2);
if (lean::is_exclusive(x_288)) {
 lean::cnstr_set(x_288, 0, lean::box(0));
 lean::cnstr_set(x_288, 1, lean::box(0));
 lean::cnstr_set(x_288, 2, lean::box(0));
 x_295 = x_288;
} else {
 lean::inc(x_289);
 lean::inc(x_291);
 lean::inc(x_293);
 lean::dec(x_288);
 x_295 = lean::box(0);
}
x_296 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_296, 0, x_289);
if (lean::is_scalar(x_295)) {
 x_297 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_297 = x_295;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_291);
lean::cnstr_set(x_297, 2, x_277);
x_298 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_293, x_297);
x_299 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_284, x_298);
x_300 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_299);
x_301 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_300);
x_302 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_301);
return x_302;
}
else
{
obj* x_303; uint8 x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_303 = lean::cnstr_get(x_288, 0);
x_305 = lean::cnstr_get_scalar<uint8>(x_288, sizeof(void*)*1);
if (lean::is_exclusive(x_288)) {
 lean::cnstr_set(x_288, 0, lean::box(0));
 x_306 = x_288;
} else {
 lean::inc(x_303);
 lean::dec(x_288);
 x_306 = lean::box(0);
}
if (lean::is_scalar(x_306)) {
 x_307 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_307 = x_306;
}
lean::cnstr_set(x_307, 0, x_303);
lean::cnstr_set_scalar(x_307, sizeof(void*)*1, x_305);
x_308 = x_307;
x_309 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_284, x_308);
x_310 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_309);
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_310);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_311);
return x_312;
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; 
lean::dec(x_0);
lean::dec(x_284);
x_315 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_279);
x_316 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_315);
x_317 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_316);
return x_317;
}
}
}
lbl_186:
{
if (x_185 == 0)
{
obj* x_318; 
x_318 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_318) == 0)
{
obj* x_319; obj* x_321; obj* x_323; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
x_319 = lean::cnstr_get(x_318, 0);
x_321 = lean::cnstr_get(x_318, 1);
x_323 = lean::cnstr_get(x_318, 2);
if (lean::is_exclusive(x_318)) {
 lean::cnstr_set(x_318, 0, lean::box(0));
 lean::cnstr_set(x_318, 1, lean::box(0));
 lean::cnstr_set(x_318, 2, lean::box(0));
 x_325 = x_318;
} else {
 lean::inc(x_319);
 lean::inc(x_321);
 lean::inc(x_323);
 lean::dec(x_318);
 x_325 = lean::box(0);
}
x_326 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_326, 0, x_319);
x_327 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_325)) {
 x_328 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_328 = x_325;
}
lean::cnstr_set(x_328, 0, x_326);
lean::cnstr_set(x_328, 1, x_321);
lean::cnstr_set(x_328, 2, x_327);
x_329 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_323, x_328);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_184, x_329);
x_331 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_330);
x_332 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_331);
x_333 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_332);
return x_333;
}
else
{
obj* x_334; uint8 x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
x_334 = lean::cnstr_get(x_318, 0);
x_336 = lean::cnstr_get_scalar<uint8>(x_318, sizeof(void*)*1);
if (lean::is_exclusive(x_318)) {
 lean::cnstr_set(x_318, 0, lean::box(0));
 x_337 = x_318;
} else {
 lean::inc(x_334);
 lean::dec(x_318);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_334);
lean::cnstr_set_scalar(x_338, sizeof(void*)*1, x_336);
x_339 = x_338;
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_184, x_339);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_340);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_341);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_342);
return x_343;
}
}
else
{
obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_0);
x_345 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_345, 0, x_184);
lean::cnstr_set_scalar(x_345, sizeof(void*)*1, x_185);
x_346 = x_345;
x_347 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_346);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_347);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_348);
return x_349;
}
}
}
}
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(x_2, x_1);
return x_3;
}
}
obj* _init_l_lean_ir_parse__uint16___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uint16");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__uint16___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("big numeral, it does not fit in an uint16");
return x_0;
}
}
obj* l_lean_ir_parse__uint16(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_13 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_7);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; 
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 2);
lean::inc(x_28);
lean::dec(x_23);
x_1 = x_24;
x_2 = x_26;
x_3 = x_28;
goto lbl_4;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_32 = lean::cnstr_get(x_23, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_32);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_37);
x_39 = l_lean_parser_parsec__t_try__mk__res___rarg(x_38);
x_40 = l_lean_ir_parse__uint16___closed__1;
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_40);
return x_41;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_13);
lean::dec(x_7);
x_44 = lean::cnstr_get(x_14, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_47 = x_14;
} else {
 lean::inc(x_44);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 2);
lean::inc(x_55);
lean::dec(x_50);
x_1 = x_51;
x_2 = x_53;
x_3 = x_55;
goto lbl_4;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_0);
x_59 = lean::cnstr_get(x_50, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 x_62 = x_50;
} else {
 lean::inc(x_59);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_64);
x_67 = l_lean_parser_parsec__t_try__mk__res___rarg(x_66);
x_68 = l_lean_ir_parse__uint16___closed__1;
x_69 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_68);
return x_69;
}
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_0);
x_71 = lean::cnstr_get(x_6, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_74 = x_6;
} else {
 lean::inc(x_71);
 lean::dec(x_6);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_76);
x_79 = l_lean_parser_parsec__t_try__mk__res___rarg(x_78);
x_80 = l_lean_ir_parse__uint16___closed__1;
x_81 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_79, x_80);
return x_81;
}
lbl_4:
{
obj* x_82; uint8 x_83; 
x_82 = l_uint16__sz;
x_83 = lean::nat_dec_le(x_82, x_1);
if (x_83 == 0)
{
uint16 x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_0);
x_85 = lean::uint16_of_nat(x_1);
lean::dec(x_1);
x_87 = l_lean_ir_keyword___closed__1;
x_88 = lean::box(x_85);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_2);
lean::cnstr_set(x_89, 2, x_87);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_89);
x_91 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_90);
x_93 = l_lean_parser_parsec__t_try__mk__res___rarg(x_92);
x_94 = l_lean_ir_parse__uint16___closed__1;
x_95 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_93, x_94);
return x_95;
}
else
{
obj* x_96; obj* x_97; 
x_96 = l_lean_ir_parse__uint16___closed__2;
x_97 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_96, x_0, x_2);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_102; uint16 x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_98 = lean::cnstr_get(x_97, 1);
x_100 = lean::cnstr_get(x_97, 2);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_set(x_97, 1, lean::box(0));
 lean::cnstr_set(x_97, 2, lean::box(0));
 x_102 = x_97;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_97);
 x_102 = lean::box(0);
}
x_103 = lean::uint16_of_nat(x_1);
lean::dec(x_1);
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_106 = lean::box(x_103);
if (lean::is_scalar(x_102)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_102;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_98);
lean::cnstr_set(x_107, 2, x_105);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_109);
x_111 = l_lean_parser_parsec__t_try__mk__res___rarg(x_110);
x_112 = l_lean_ir_parse__uint16___closed__1;
x_113 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_111, x_112);
return x_113;
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_1);
x_115 = lean::cnstr_get(x_97, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_set(x_97, 0, lean::box(0));
 x_118 = x_97;
} else {
 lean::inc(x_115);
 lean::dec(x_97);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_120);
x_122 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_121);
x_124 = l_lean_parser_parsec__t_try__mk__res___rarg(x_123);
x_125 = l_lean_ir_parse__uint16___closed__1;
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_124, x_125);
return x_126;
}
}
}
}
}
obj* _init_l_lean_ir_parse__usize___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("usize");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__usize___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("big numeral, it does not fit in an usize");
return x_0;
}
}
obj* l_lean_ir_parse__usize(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_13 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_7);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; 
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 2);
lean::inc(x_28);
lean::dec(x_23);
x_1 = x_24;
x_2 = x_26;
x_3 = x_28;
goto lbl_4;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_32 = lean::cnstr_get(x_23, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_35 = x_23;
} else {
 lean::inc(x_32);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_37);
x_39 = l_lean_parser_parsec__t_try__mk__res___rarg(x_38);
x_40 = l_lean_ir_parse__usize___closed__1;
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_40);
return x_41;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_13);
lean::dec(x_7);
x_44 = lean::cnstr_get(x_14, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_47 = x_14;
} else {
 lean::inc(x_44);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_55; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 2);
lean::inc(x_55);
lean::dec(x_50);
x_1 = x_51;
x_2 = x_53;
x_3 = x_55;
goto lbl_4;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_0);
x_59 = lean::cnstr_get(x_50, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 x_62 = x_50;
} else {
 lean::inc(x_59);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_64);
x_67 = l_lean_parser_parsec__t_try__mk__res___rarg(x_66);
x_68 = l_lean_ir_parse__usize___closed__1;
x_69 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_68);
return x_69;
}
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_0);
x_71 = lean::cnstr_get(x_6, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_74 = x_6;
} else {
 lean::inc(x_71);
 lean::dec(x_6);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_76);
x_79 = l_lean_parser_parsec__t_try__mk__res___rarg(x_78);
x_80 = l_lean_ir_parse__usize___closed__1;
x_81 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_79, x_80);
return x_81;
}
lbl_4:
{
obj* x_82; uint8 x_83; 
x_82 = l_usize__sz;
x_83 = lean::nat_dec_le(x_82, x_1);
if (x_83 == 0)
{
usize x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_0);
x_85 = lean::usize_of_nat(x_1);
lean::dec(x_1);
x_87 = l_lean_ir_keyword___closed__1;
x_88 = lean::box_size_t(x_85);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_2);
lean::cnstr_set(x_89, 2, x_87);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_89);
x_91 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_90);
x_93 = l_lean_parser_parsec__t_try__mk__res___rarg(x_92);
x_94 = l_lean_ir_parse__usize___closed__1;
x_95 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_93, x_94);
return x_95;
}
else
{
obj* x_96; obj* x_97; 
x_96 = l_lean_ir_parse__usize___closed__2;
x_97 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_96, x_0, x_2);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_102; usize x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_98 = lean::cnstr_get(x_97, 1);
x_100 = lean::cnstr_get(x_97, 2);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_set(x_97, 1, lean::box(0));
 lean::cnstr_set(x_97, 2, lean::box(0));
 x_102 = x_97;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_97);
 x_102 = lean::box(0);
}
x_103 = lean::usize_of_nat(x_1);
lean::dec(x_1);
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_106 = lean::box_size_t(x_103);
if (lean::is_scalar(x_102)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_102;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_98);
lean::cnstr_set(x_107, 2, x_105);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_109);
x_111 = l_lean_parser_parsec__t_try__mk__res___rarg(x_110);
x_112 = l_lean_ir_parse__usize___closed__1;
x_113 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_111, x_112);
return x_113;
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_1);
x_115 = lean::cnstr_get(x_97, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_set(x_97, 0, lean::box(0));
 x_118 = x_97;
} else {
 lean::inc(x_115);
 lean::dec(x_97);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_120);
x_122 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_121);
x_124 = l_lean_parser_parsec__t_try__mk__res___rarg(x_123);
x_125 = l_lean_ir_parse__usize___closed__1;
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_124, x_125);
return x_126;
}
}
}
}
}
obj* l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_curr(x_0);
x_2 = l_lean_ir_keyword___closed__1;
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__6(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__rest(x_8);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__6(x_4, x_3, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__8(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__rest(x_8);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__8(x_4, x_3, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__10(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__rest(x_8);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_2);
x_6 = lean::string_iterator_remaining(x_1);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__10(x_6, x_5, x_1);
return x_7;
}
}
obj* l_lean_parser_id__part__default___at_lean_ir_identifier___spec__4(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_16 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(x_15, x_10);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
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
x_25 = l_lean_is__id__first(x_24);
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
x_33 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_30, x_32, x_31, x_31, x_0);
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
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(x_43, x_38);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_44);
return x_45;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_35, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
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
x_55 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(x_0, x_53);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_55);
return x_56;
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__14(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__14(x_4, x_3, x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_2);
x_6 = lean::string_iterator_remaining(x_1);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(x_6, x_5, x_1);
return x_7;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__18(obj* x_0, obj* x_1, obj* x_2) {
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
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__18(x_4, x_3, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_identifier___spec__12(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_16 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13(x_15, x_10);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_7, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
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
x_25 = l_lean_is__id__end__escape(x_24);
if (x_25 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::inc(x_0);
x_27 = lean::string_iterator_next(x_0);
x_28 = lean::box(0);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15(x_0, x_27);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_29);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_31 = l_char_quote__core(x_24);
x_32 = l_char_has__repr___closed__1;
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_35 = lean::string_append(x_33, x_32);
x_36 = lean::box(0);
x_37 = l_mjoin___rarg___closed__1;
x_38 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_35, x_37, x_36, x_36, x_0);
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_38);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_45; uint32 x_48; obj* x_49; obj* x_50; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 2);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::unbox_uint32(x_41);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(x_48, x_43);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_49);
return x_50;
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_40, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 x_54 = x_40;
} else {
 lean::inc(x_51);
 lean::dec(x_40);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
return x_56;
}
}
}
}
}
obj* l_lean_parser_id__part__escaped___at_lean_ir_identifier___spec__11(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_lean_id__begin__escape;
x_2 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_lean_parser_monad__parsec_take__while1___at_lean_ir_identifier___spec__12(x_3);
x_9 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; uint32 x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
lean::dec(x_9);
x_17 = l_lean_id__end__escape;
x_18 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_17, x_12);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_7)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_7;
}
lean::cnstr_set(x_25, 0, x_10);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_26);
return x_27;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_7);
lean::dec(x_10);
x_30 = lean::cnstr_get(x_18, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_33 = x_18;
} else {
 lean::inc(x_30);
 lean::dec(x_18);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_35);
return x_36;
}
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_7);
x_38 = lean::cnstr_get(x_9, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_41 = x_9;
} else {
 lean::inc(x_38);
 lean::dec(x_9);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
return x_43;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_2, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_47 = x_2;
} else {
 lean::inc(x_44);
 lean::dec(x_2);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
return x_49;
}
}
}
obj* l_lean_parser_id__part___at_lean_ir_identifier___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; uint32 x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::unbox_uint32(x_2);
x_10 = l_lean_is__id__begin__escape(x_9);
x_11 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_12 = lean::box(x_10);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
lean::cnstr_set(x_13, 2, x_11);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; uint8 x_22; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 2);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::unbox(x_15);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = l_lean_parser_id__part__default___at_lean_ir_identifier___spec__4(x_17);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_lean_parser_id__part__escaped___at_lean_ir_identifier___spec__11(x_17);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_25);
return x_26;
}
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_14, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_30 = x_14;
} else {
 lean::inc(x_27);
 lean::dec(x_14);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
return x_32;
}
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_36 = x_1;
} else {
 lean::inc(x_33);
 lean::dec(x_1);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
return x_38;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32 x_5; obj* x_7; 
x_5 = 46;
lean::inc(x_2);
x_7 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_7, 1);
x_10 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_12 = x_7;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = l_lean_parser_id__part___at_lean_ir_identifier___spec__2(x_8);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 2);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_sub(x_1, x_22);
lean::dec(x_1);
lean::inc(x_0);
x_26 = lean_name_mk_string(x_0, x_15);
x_27 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_26, x_23, x_17);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
if (lean::obj_tag(x_28) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
return x_28;
}
else
{
obj* x_32; uint8 x_34; 
x_32 = lean::cnstr_get(x_28, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (x_34 == 0)
{
obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_28);
x_36 = lean::cnstr_get(x_32, 2);
lean::inc(x_36);
lean::dec(x_32);
x_39 = l_mjoin___rarg___closed__1;
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
if (lean::is_scalar(x_12)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_12;
}
lean::cnstr_set(x_42, 0, x_0);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_41);
return x_42;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
lean::dec(x_32);
return x_28;
}
}
}
else
{
obj* x_48; uint8 x_50; obj* x_51; 
lean::dec(x_1);
x_48 = lean::cnstr_get(x_14, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_51 = x_14;
} else {
 lean::inc(x_48);
 lean::dec(x_14);
 x_51 = lean::box(0);
}
if (x_50 == 0)
{
obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_51);
x_53 = lean::cnstr_get(x_48, 2);
lean::inc(x_53);
lean::dec(x_48);
x_56 = l_mjoin___rarg___closed__1;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_57, 0, x_53);
lean::closure_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
if (lean::is_scalar(x_12)) {
 x_59 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_59 = x_12;
}
lean::cnstr_set(x_59, 0, x_0);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
else
{
obj* x_63; obj* x_64; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
if (lean::is_scalar(x_51)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_51;
}
lean::cnstr_set(x_63, 0, x_48);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_50);
x_64 = x_63;
return x_64;
}
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; 
lean::dec(x_1);
x_66 = lean::cnstr_get(x_7, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_69 = x_7;
} else {
 lean::inc(x_66);
 lean::dec(x_7);
 x_69 = lean::box(0);
}
if (x_68 == 0)
{
obj* x_71; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = l_mjoin___rarg___closed__1;
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_75, 0, x_71);
lean::closure_set(x_75, 1, x_74);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_0);
lean::cnstr_set(x_77, 1, x_2);
lean::cnstr_set(x_77, 2, x_76);
return x_77;
}
else
{
obj* x_80; obj* x_81; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_69)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_69;
}
lean::cnstr_set(x_80, 0, x_66);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_68);
x_81 = x_80;
return x_81;
}
}
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_1);
x_83 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_0);
lean::cnstr_set(x_84, 1, x_2);
lean::cnstr_set(x_84, 2, x_83);
return x_84;
}
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_ir_identifier___spec__19(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::box(0);
x_3 = lean_name_mk_string(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_3, x_4, x_1);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_5);
return x_7;
}
}
obj* _init_l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_id__part___at_lean_ir_identifier___spec__2(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_parser_monad__parsec_foldl___at_lean_ir_identifier___spec__19(x_2, x_4);
x_10 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
x_11 = l_lean_parser_parsec__t_try__mk__res___rarg(x_10);
x_12 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_13 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_11, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 3);
lean::inc(x_21);
lean::dec(x_14);
x_24 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_17);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_21);
x_26 = 0;
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_26);
x_28 = x_27;
return x_28;
}
}
}
obj* _init_l_lean_ir_identifier___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("keyword");
return x_0;
}
}
obj* l_lean_ir_identifier(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_11; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
lean::inc(x_3);
x_11 = l_lean_ir_is__reserved__name___main(x_3);
if (x_11 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_0);
x_13 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_5);
lean::cnstr_set(x_14, 2, x_13);
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_14);
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_15);
x_18 = l_lean_parser_parsec__t_try__mk__res___rarg(x_17);
x_19 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_20 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_18, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = l_lean_ir_identifier___closed__1;
x_22 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_21, x_0, x_5);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 2);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_3);
lean::cnstr_set(x_29, 1, x_23);
lean::cnstr_set(x_29, 2, x_28);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_31);
x_33 = l_lean_parser_parsec__t_try__mk__res___rarg(x_32);
x_34 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_35 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_33, x_34);
return x_35;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_9);
lean::dec(x_3);
x_38 = lean::cnstr_get(x_22, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_41 = x_22;
} else {
 lean::inc(x_38);
 lean::dec(x_22);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_43);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_44);
x_47 = l_lean_parser_parsec__t_try__mk__res___rarg(x_46);
x_48 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_49 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_47, x_48);
return x_49;
}
}
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_0);
x_51 = lean::cnstr_get(x_2, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_54 = x_2;
} else {
 lean::inc(x_51);
 lean::dec(x_2);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_56);
x_59 = l_lean_parser_parsec__t_try__mk__res___rarg(x_58);
x_60 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_61 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_59, x_60);
return x_61;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(x_2, x_1);
return x_3;
}
}
obj* _init_l_lean_ir_parse__var___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("variable");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_parse__var(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_identifier(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_17);
x_19 = l_lean_ir_parse__var___closed__1;
x_20 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_18, x_19);
return x_20;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_8);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_9, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_26 = x_9;
} else {
 lean::inc(x_23);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_28);
x_30 = l_lean_ir_parse__var___closed__1;
x_31 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_29, x_30);
return x_31;
}
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_1, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_35 = x_1;
} else {
 lean::inc(x_32);
 lean::dec(x_1);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_38 = l_lean_ir_parse__var___closed__1;
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_37, x_38);
return x_39;
}
}
}
obj* _init_l_lean_ir_parse__fnid___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("function name");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_parse__fnid(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_identifier(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_17);
x_19 = l_lean_ir_parse__fnid___closed__1;
x_20 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_18, x_19);
return x_20;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_8);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_9, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_26 = x_9;
} else {
 lean::inc(x_23);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_28);
x_30 = l_lean_ir_parse__fnid___closed__1;
x_31 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_29, x_30);
return x_31;
}
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_1, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_35 = x_1;
} else {
 lean::inc(x_32);
 lean::dec(x_1);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_38 = l_lean_ir_parse__fnid___closed__1;
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_37, x_38);
return x_39;
}
}
}
obj* _init_l_lean_ir_parse__blockid___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("label");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_parse__blockid(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_identifier(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 2);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_8;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_17);
x_19 = l_lean_ir_parse__blockid___closed__1;
x_20 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_18, x_19);
return x_20;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_8);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_9, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_26 = x_9;
} else {
 lean::inc(x_23);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_28);
x_30 = l_lean_ir_parse__blockid___closed__1;
x_31 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_29, x_30);
return x_31;
}
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_1, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_35 = x_1;
} else {
 lean::inc(x_32);
 lean::dec(x_1);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_38 = l_lean_ir_parse__blockid___closed__1;
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_37, x_38);
return x_39;
}
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__1(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::alloc_cnstr(3, 3, 2);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*3, x_1);
x_6 = x_5;
lean::cnstr_set_scalar(x_6, sizeof(void*)*3 + 1, x_2);
x_7 = x_6;
return x_7;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__2(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(2, 2, 2);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_1);
x_5 = x_4;
lean::cnstr_set_scalar(x_5, sizeof(void*)*2 + 1, x_2);
x_6 = x_5;
return x_6;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__3(obj* x_0, uint8 x_1, obj* x_2, usize x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(10, 2, sizeof(size_t)*1 + 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_1);
x_5 = x_4;
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
x_6 = x_5;
return x_6;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("type");
return x_0;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":=");
return x_0;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("binary operator");
return x_0;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unary operator");
return x_0;
}
}
obj* _init_l_lean_ir_parse__typed__assignment___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("sget");
return x_0;
}
}
obj* l_lean_ir_parse__typed__assignment(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_parse__typed__assignment___closed__1;
x_3 = l_lean_ir_symbol(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_lean_ir_parse__typed__assignment___closed__2;
x_10 = l_lean_ir_str2type;
x_11 = l_lean_ir_parse__key2val___main___rarg(x_9, x_10, x_4);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_11, 0);
x_14 = lean::cnstr_get(x_11, 1);
x_16 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_18 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_parse__typed__assignment___closed__3;
x_20 = l_lean_ir_symbol(x_19, x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; 
x_21 = lean::cnstr_get(x_20, 1);
x_23 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_set(x_20, 1, lean::box(0));
 lean::cnstr_set(x_20, 2, lean::box(0));
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_32 = l_lean_ir_parse__typed__assignment___closed__6;
lean::inc(x_21);
x_34 = l_lean_ir_keyword(x_32, x_21);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_34, 1);
x_37 = lean::cnstr_get(x_34, 2);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_set(x_34, 1, lean::box(0));
 lean::cnstr_set(x_34, 2, lean::box(0));
 x_39 = x_34;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_34);
 x_39 = lean::box(0);
}
x_40 = l_lean_ir_parse__var(x_35);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 2);
lean::inc(x_45);
lean::dec(x_40);
lean::inc(x_12);
lean::inc(x_0);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__3___boxed), 4, 3);
lean::closure_set(x_50, 0, x_0);
lean::closure_set(x_50, 1, x_12);
lean::closure_set(x_50, 2, x_41);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_43);
lean::cnstr_set(x_52, 2, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 2);
lean::inc(x_59);
lean::dec(x_54);
x_28 = x_55;
x_29 = x_57;
x_30 = x_59;
goto lbl_31;
}
else
{
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_54, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_set(x_54, 0, lean::box(0));
 x_65 = x_54;
} else {
 lean::inc(x_62);
 lean::dec(x_54);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_26 = x_67;
goto lbl_27;
}
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_39);
x_69 = lean::cnstr_get(x_40, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_set(x_40, 0, lean::box(0));
 x_72 = x_40;
} else {
 lean::inc(x_69);
 lean::dec(x_40);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
x_28 = x_76;
x_29 = x_78;
x_30 = x_80;
goto lbl_31;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_75, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 x_86 = x_75;
} else {
 lean::inc(x_83);
 lean::dec(x_75);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
x_26 = x_88;
goto lbl_27;
}
}
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; 
x_89 = lean::cnstr_get(x_34, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_set(x_34, 0, lean::box(0));
 x_92 = x_34;
} else {
 lean::inc(x_89);
 lean::dec(x_34);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_26 = x_94;
goto lbl_27;
}
lbl_27:
{
if (lean::obj_tag(x_26) == 0)
{
obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_102);
return x_103;
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; uint8 x_109; 
x_104 = lean::cnstr_get(x_26, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_106 == 0)
{
obj* x_113; 
lean::dec(x_26);
lean::inc(x_21);
x_113 = l_lean_ir_parse__var(x_21);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_122; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_114 = lean::cnstr_get(x_113, 0);
x_116 = lean::cnstr_get(x_113, 1);
x_118 = lean::cnstr_get(x_113, 2);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_set(x_113, 0, lean::box(0));
 lean::cnstr_set(x_113, 1, lean::box(0));
 lean::cnstr_set(x_113, 2, lean::box(0));
 x_120 = x_113;
} else {
 lean::inc(x_114);
 lean::inc(x_116);
 lean::inc(x_118);
 lean::dec(x_113);
 x_120 = lean::box(0);
}
lean::inc(x_0);
x_122 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_122, 0, x_0);
lean::cnstr_set(x_122, 1, x_114);
x_123 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_122, sizeof(void*)*2, x_123);
x_124 = x_122;
x_125 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_120)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_120;
}
lean::cnstr_set(x_126, 0, x_124);
lean::cnstr_set(x_126, 1, x_116);
lean::cnstr_set(x_126, 2, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_133 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_127);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_135);
return x_136;
}
else
{
obj* x_137; uint8 x_139; 
x_137 = lean::cnstr_get(x_127, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
x_107 = x_127;
x_108 = x_137;
x_109 = x_139;
goto lbl_110;
}
}
else
{
obj* x_140; uint8 x_142; obj* x_143; obj* x_145; obj* x_146; 
x_140 = lean::cnstr_get(x_113, 0);
x_142 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_set(x_113, 0, lean::box(0));
 x_143 = x_113;
} else {
 lean::inc(x_140);
 lean::dec(x_113);
 x_143 = lean::box(0);
}
lean::inc(x_140);
if (lean::is_scalar(x_143)) {
 x_145 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_145 = x_143;
}
lean::cnstr_set(x_145, 0, x_140);
lean::cnstr_set_scalar(x_145, sizeof(void*)*1, x_142);
x_146 = x_145;
x_107 = x_146;
x_108 = x_140;
x_109 = x_142;
goto lbl_110;
}
}
else
{
obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
lean::dec(x_104);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_154);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_155);
return x_156;
}
lbl_110:
{
obj* x_157; obj* x_158; uint8 x_159; 
if (x_109 == 0)
{
obj* x_162; obj* x_163; obj* x_165; 
lean::dec(x_107);
x_162 = l_lean_ir_parse__typed__assignment___closed__5;
x_163 = l_lean_ir_str2aunop;
lean::inc(x_21);
x_165 = l_lean_ir_parse__key2val___main___rarg(x_162, x_163, x_21);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_166 = lean::cnstr_get(x_165, 0);
x_168 = lean::cnstr_get(x_165, 1);
x_170 = lean::cnstr_get(x_165, 2);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_set(x_165, 0, lean::box(0));
 lean::cnstr_set(x_165, 1, lean::box(0));
 lean::cnstr_set(x_165, 2, lean::box(0));
 x_172 = x_165;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_165);
 x_172 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_175 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__2___boxed), 4, 3);
lean::closure_set(x_175, 0, x_0);
lean::closure_set(x_175, 1, x_12);
lean::closure_set(x_175, 2, x_166);
x_176 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_172)) {
 x_177 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_177 = x_172;
}
lean::cnstr_set(x_177, 0, x_175);
lean::cnstr_set(x_177, 1, x_168);
lean::cnstr_set(x_177, 2, x_176);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_177);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
x_179 = lean::cnstr_get(x_178, 0);
x_181 = lean::cnstr_get(x_178, 1);
x_183 = lean::cnstr_get(x_178, 2);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_set(x_178, 0, lean::box(0));
 lean::cnstr_set(x_178, 1, lean::box(0));
 lean::cnstr_set(x_178, 2, lean::box(0));
 x_185 = x_178;
} else {
 lean::inc(x_179);
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_178);
 x_185 = lean::box(0);
}
x_186 = l_lean_ir_parse__var(x_181);
if (lean::obj_tag(x_186) == 0)
{
obj* x_187; obj* x_189; obj* x_191; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_186, 2);
lean::inc(x_191);
lean::dec(x_186);
x_194 = lean::apply_1(x_179, x_187);
if (lean::is_scalar(x_185)) {
 x_195 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_195 = x_185;
}
lean::cnstr_set(x_195, 0, x_194);
lean::cnstr_set(x_195, 1, x_189);
lean::cnstr_set(x_195, 2, x_176);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_191, x_195);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_196);
if (lean::obj_tag(x_197) == 0)
{
obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_197);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_204);
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_205);
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_206);
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_207);
return x_208;
}
else
{
obj* x_209; uint8 x_211; 
x_209 = lean::cnstr_get(x_197, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*1);
x_157 = x_197;
x_158 = x_209;
x_159 = x_211;
goto lbl_160;
}
}
else
{
obj* x_214; uint8 x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
lean::dec(x_179);
lean::dec(x_185);
x_214 = lean::cnstr_get(x_186, 0);
x_216 = lean::cnstr_get_scalar<uint8>(x_186, sizeof(void*)*1);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_set(x_186, 0, lean::box(0));
 x_217 = x_186;
} else {
 lean::inc(x_214);
 lean::dec(x_186);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_214);
lean::cnstr_set_scalar(x_218, sizeof(void*)*1, x_216);
x_219 = x_218;
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_227 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_220);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_227);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_228);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_230);
return x_231;
}
else
{
obj* x_232; uint8 x_234; 
x_232 = lean::cnstr_get(x_220, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get_scalar<uint8>(x_220, sizeof(void*)*1);
x_157 = x_220;
x_158 = x_232;
x_159 = x_234;
goto lbl_160;
}
}
}
else
{
obj* x_235; uint8 x_237; obj* x_238; obj* x_240; obj* x_241; 
x_235 = lean::cnstr_get(x_178, 0);
x_237 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_set(x_178, 0, lean::box(0));
 x_238 = x_178;
} else {
 lean::inc(x_235);
 lean::dec(x_178);
 x_238 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_238)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_238;
}
lean::cnstr_set(x_240, 0, x_235);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_237);
x_241 = x_240;
x_157 = x_241;
x_158 = x_235;
x_159 = x_237;
goto lbl_160;
}
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_247; obj* x_248; 
x_242 = lean::cnstr_get(x_165, 0);
x_244 = lean::cnstr_get_scalar<uint8>(x_165, sizeof(void*)*1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_set(x_165, 0, lean::box(0));
 x_245 = x_165;
} else {
 lean::inc(x_242);
 lean::dec(x_165);
 x_245 = lean::box(0);
}
lean::inc(x_242);
if (lean::is_scalar(x_245)) {
 x_247 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_247 = x_245;
}
lean::cnstr_set(x_247, 0, x_242);
lean::cnstr_set_scalar(x_247, sizeof(void*)*1, x_244);
x_248 = x_247;
x_157 = x_248;
x_158 = x_242;
x_159 = x_244;
goto lbl_160;
}
}
else
{
obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_108);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_256 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_107);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_256);
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_257);
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_258);
return x_259;
}
lbl_160:
{
obj* x_260; obj* x_261; uint8 x_262; obj* x_264; obj* x_265; obj* x_266; 
if (x_159 == 0)
{
obj* x_269; obj* x_270; obj* x_272; 
lean::dec(x_157);
x_269 = l_lean_ir_parse__typed__assignment___closed__4;
x_270 = l_lean_ir_str2abinop;
lean::inc(x_21);
x_272 = l_lean_ir_parse__key2val___main___rarg(x_269, x_270, x_21);
if (lean::obj_tag(x_272) == 0)
{
obj* x_273; obj* x_275; obj* x_277; obj* x_279; obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
x_273 = lean::cnstr_get(x_272, 0);
x_275 = lean::cnstr_get(x_272, 1);
x_277 = lean::cnstr_get(x_272, 2);
if (lean::is_exclusive(x_272)) {
 lean::cnstr_set(x_272, 0, lean::box(0));
 lean::cnstr_set(x_272, 1, lean::box(0));
 lean::cnstr_set(x_272, 2, lean::box(0));
 x_279 = x_272;
} else {
 lean::inc(x_273);
 lean::inc(x_275);
 lean::inc(x_277);
 lean::dec(x_272);
 x_279 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_282 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__1___boxed), 5, 3);
lean::closure_set(x_282, 0, x_0);
lean::closure_set(x_282, 1, x_12);
lean::closure_set(x_282, 2, x_273);
x_283 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_284 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_284 = x_25;
}
lean::cnstr_set(x_284, 0, x_282);
lean::cnstr_set(x_284, 1, x_275);
lean::cnstr_set(x_284, 2, x_283);
x_285 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_284);
if (lean::obj_tag(x_285) == 0)
{
obj* x_286; obj* x_288; obj* x_290; obj* x_293; 
x_286 = lean::cnstr_get(x_285, 0);
lean::inc(x_286);
x_288 = lean::cnstr_get(x_285, 1);
lean::inc(x_288);
x_290 = lean::cnstr_get(x_285, 2);
lean::inc(x_290);
lean::dec(x_285);
x_293 = l_lean_ir_parse__var(x_288);
if (lean::obj_tag(x_293) == 0)
{
obj* x_294; obj* x_296; obj* x_298; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
x_294 = lean::cnstr_get(x_293, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_293, 1);
lean::inc(x_296);
x_298 = lean::cnstr_get(x_293, 2);
lean::inc(x_298);
lean::dec(x_293);
x_301 = lean::apply_1(x_286, x_294);
if (lean::is_scalar(x_279)) {
 x_302 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_302 = x_279;
}
lean::cnstr_set(x_302, 0, x_301);
lean::cnstr_set(x_302, 1, x_296);
lean::cnstr_set(x_302, 2, x_283);
x_303 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_298, x_302);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_303);
if (lean::obj_tag(x_304) == 0)
{
obj* x_305; obj* x_307; obj* x_309; 
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_304, 2);
lean::inc(x_309);
lean::dec(x_304);
x_264 = x_305;
x_265 = x_307;
x_266 = x_309;
goto lbl_267;
}
else
{
obj* x_313; uint8 x_315; obj* x_316; obj* x_318; obj* x_319; 
lean::dec(x_18);
x_313 = lean::cnstr_get(x_304, 0);
x_315 = lean::cnstr_get_scalar<uint8>(x_304, sizeof(void*)*1);
if (lean::is_exclusive(x_304)) {
 lean::cnstr_set(x_304, 0, lean::box(0));
 x_316 = x_304;
} else {
 lean::inc(x_313);
 lean::dec(x_304);
 x_316 = lean::box(0);
}
lean::inc(x_313);
if (lean::is_scalar(x_316)) {
 x_318 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_318 = x_316;
}
lean::cnstr_set(x_318, 0, x_313);
lean::cnstr_set_scalar(x_318, sizeof(void*)*1, x_315);
x_319 = x_318;
x_260 = x_319;
x_261 = x_313;
x_262 = x_315;
goto lbl_263;
}
}
else
{
obj* x_322; uint8 x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
lean::dec(x_279);
lean::dec(x_286);
x_322 = lean::cnstr_get(x_293, 0);
x_324 = lean::cnstr_get_scalar<uint8>(x_293, sizeof(void*)*1);
if (lean::is_exclusive(x_293)) {
 lean::cnstr_set(x_293, 0, lean::box(0));
 x_325 = x_293;
} else {
 lean::inc(x_322);
 lean::dec(x_293);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_322);
lean::cnstr_set_scalar(x_326, sizeof(void*)*1, x_324);
x_327 = x_326;
x_328 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_327);
if (lean::obj_tag(x_328) == 0)
{
obj* x_329; obj* x_331; obj* x_333; 
x_329 = lean::cnstr_get(x_328, 0);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_328, 1);
lean::inc(x_331);
x_333 = lean::cnstr_get(x_328, 2);
lean::inc(x_333);
lean::dec(x_328);
x_264 = x_329;
x_265 = x_331;
x_266 = x_333;
goto lbl_267;
}
else
{
obj* x_337; uint8 x_339; obj* x_340; obj* x_342; obj* x_343; 
lean::dec(x_18);
x_337 = lean::cnstr_get(x_328, 0);
x_339 = lean::cnstr_get_scalar<uint8>(x_328, sizeof(void*)*1);
if (lean::is_exclusive(x_328)) {
 lean::cnstr_set(x_328, 0, lean::box(0));
 x_340 = x_328;
} else {
 lean::inc(x_337);
 lean::dec(x_328);
 x_340 = lean::box(0);
}
lean::inc(x_337);
if (lean::is_scalar(x_340)) {
 x_342 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_342 = x_340;
}
lean::cnstr_set(x_342, 0, x_337);
lean::cnstr_set_scalar(x_342, sizeof(void*)*1, x_339);
x_343 = x_342;
x_260 = x_343;
x_261 = x_337;
x_262 = x_339;
goto lbl_263;
}
}
}
else
{
obj* x_346; uint8 x_348; obj* x_349; obj* x_351; obj* x_352; 
lean::dec(x_18);
lean::dec(x_279);
x_346 = lean::cnstr_get(x_285, 0);
x_348 = lean::cnstr_get_scalar<uint8>(x_285, sizeof(void*)*1);
if (lean::is_exclusive(x_285)) {
 lean::cnstr_set(x_285, 0, lean::box(0));
 x_349 = x_285;
} else {
 lean::inc(x_346);
 lean::dec(x_285);
 x_349 = lean::box(0);
}
lean::inc(x_346);
if (lean::is_scalar(x_349)) {
 x_351 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_351 = x_349;
}
lean::cnstr_set(x_351, 0, x_346);
lean::cnstr_set_scalar(x_351, sizeof(void*)*1, x_348);
x_352 = x_351;
x_260 = x_352;
x_261 = x_346;
x_262 = x_348;
goto lbl_263;
}
}
else
{
obj* x_355; uint8 x_357; obj* x_358; obj* x_360; obj* x_361; 
lean::dec(x_18);
lean::dec(x_25);
x_355 = lean::cnstr_get(x_272, 0);
x_357 = lean::cnstr_get_scalar<uint8>(x_272, sizeof(void*)*1);
if (lean::is_exclusive(x_272)) {
 lean::cnstr_set(x_272, 0, lean::box(0));
 x_358 = x_272;
} else {
 lean::inc(x_355);
 lean::dec(x_272);
 x_358 = lean::box(0);
}
lean::inc(x_355);
if (lean::is_scalar(x_358)) {
 x_360 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_360 = x_358;
}
lean::cnstr_set(x_360, 0, x_355);
lean::cnstr_set_scalar(x_360, sizeof(void*)*1, x_357);
x_361 = x_360;
x_260 = x_361;
x_261 = x_355;
x_262 = x_357;
goto lbl_263;
}
}
else
{
obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
lean::dec(x_158);
x_369 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_157);
x_370 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_369);
x_371 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_370);
x_372 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_371);
x_373 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_372);
return x_373;
}
lbl_263:
{
if (x_262 == 0)
{
obj* x_375; 
lean::dec(x_260);
x_375 = l_lean_ir_parse__literal(x_21);
if (lean::obj_tag(x_375) == 0)
{
obj* x_376; obj* x_378; obj* x_380; obj* x_383; uint8 x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; 
x_376 = lean::cnstr_get(x_375, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_375, 1);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_375, 2);
lean::inc(x_380);
lean::dec(x_375);
x_383 = lean::alloc_cnstr(1, 2, 1);
lean::cnstr_set(x_383, 0, x_0);
lean::cnstr_set(x_383, 1, x_376);
x_384 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_383, sizeof(void*)*2, x_384);
x_385 = x_383;
x_386 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_387 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_387 = x_8;
}
lean::cnstr_set(x_387, 0, x_385);
lean::cnstr_set(x_387, 1, x_378);
lean::cnstr_set(x_387, 2, x_386);
x_388 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_380, x_387);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_261, x_388);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_389);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_390);
x_392 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_391);
x_393 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_392);
x_394 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_393);
x_395 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_394);
return x_395;
}
else
{
obj* x_399; uint8 x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
x_399 = lean::cnstr_get(x_375, 0);
x_401 = lean::cnstr_get_scalar<uint8>(x_375, sizeof(void*)*1);
if (lean::is_exclusive(x_375)) {
 lean::cnstr_set(x_375, 0, lean::box(0));
 x_402 = x_375;
} else {
 lean::inc(x_399);
 lean::dec(x_375);
 x_402 = lean::box(0);
}
if (lean::is_scalar(x_402)) {
 x_403 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_403 = x_402;
}
lean::cnstr_set(x_403, 0, x_399);
lean::cnstr_set_scalar(x_403, sizeof(void*)*1, x_401);
x_404 = x_403;
x_405 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_261, x_404);
x_406 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_405);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_407);
x_409 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_408);
x_410 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_409);
x_411 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_410);
return x_411;
}
}
else
{
obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_261);
lean::dec(x_21);
x_417 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_260);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_417);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_418);
x_420 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_419);
x_421 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_420);
x_422 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_421);
return x_422;
}
}
lbl_267:
{
obj* x_423; 
x_423 = l_lean_ir_parse__var(x_265);
if (lean::obj_tag(x_423) == 0)
{
obj* x_424; obj* x_426; obj* x_428; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; 
x_424 = lean::cnstr_get(x_423, 0);
lean::inc(x_424);
x_426 = lean::cnstr_get(x_423, 1);
lean::inc(x_426);
x_428 = lean::cnstr_get(x_423, 2);
lean::inc(x_428);
lean::dec(x_423);
x_431 = lean::apply_1(x_264, x_424);
x_432 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_433 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_433 = x_18;
}
lean::cnstr_set(x_433, 0, x_431);
lean::cnstr_set(x_433, 1, x_426);
lean::cnstr_set(x_433, 2, x_432);
x_434 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_428, x_433);
x_435 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_434);
if (lean::obj_tag(x_435) == 0)
{
obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
x_440 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_435);
x_441 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_440);
x_442 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_441);
x_443 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_442);
x_444 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_443);
x_445 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_444);
return x_445;
}
else
{
obj* x_446; uint8 x_448; 
x_446 = lean::cnstr_get(x_435, 0);
lean::inc(x_446);
x_448 = lean::cnstr_get_scalar<uint8>(x_435, sizeof(void*)*1);
x_260 = x_435;
x_261 = x_446;
x_262 = x_448;
goto lbl_263;
}
}
else
{
obj* x_451; uint8 x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; 
lean::dec(x_264);
lean::dec(x_18);
x_451 = lean::cnstr_get(x_423, 0);
x_453 = lean::cnstr_get_scalar<uint8>(x_423, sizeof(void*)*1);
if (lean::is_exclusive(x_423)) {
 lean::cnstr_set(x_423, 0, lean::box(0));
 x_454 = x_423;
} else {
 lean::inc(x_451);
 lean::dec(x_423);
 x_454 = lean::box(0);
}
if (lean::is_scalar(x_454)) {
 x_455 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_455 = x_454;
}
lean::cnstr_set(x_455, 0, x_451);
lean::cnstr_set_scalar(x_455, sizeof(void*)*1, x_453);
x_456 = x_455;
x_457 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_266, x_456);
if (lean::obj_tag(x_457) == 0)
{
obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
x_462 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_457);
x_463 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_462);
x_464 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_463);
x_465 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_464);
x_466 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_465);
x_467 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_466);
return x_467;
}
else
{
obj* x_468; uint8 x_470; 
x_468 = lean::cnstr_get(x_457, 0);
lean::inc(x_468);
x_470 = lean::cnstr_get_scalar<uint8>(x_457, sizeof(void*)*1);
x_260 = x_457;
x_261 = x_468;
x_262 = x_470;
goto lbl_263;
}
}
}
}
}
}
}
lbl_31:
{
obj* x_471; 
x_471 = l_lean_ir_parse__usize(x_29);
if (lean::obj_tag(x_471) == 0)
{
obj* x_472; obj* x_474; obj* x_476; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; 
x_472 = lean::cnstr_get(x_471, 0);
x_474 = lean::cnstr_get(x_471, 1);
x_476 = lean::cnstr_get(x_471, 2);
if (lean::is_exclusive(x_471)) {
 lean::cnstr_set(x_471, 0, lean::box(0));
 lean::cnstr_set(x_471, 1, lean::box(0));
 lean::cnstr_set(x_471, 2, lean::box(0));
 x_478 = x_471;
} else {
 lean::inc(x_472);
 lean::inc(x_474);
 lean::inc(x_476);
 lean::dec(x_471);
 x_478 = lean::box(0);
}
x_479 = lean::apply_1(x_28, x_472);
x_480 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_478)) {
 x_481 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_481 = x_478;
}
lean::cnstr_set(x_481, 0, x_479);
lean::cnstr_set(x_481, 1, x_474);
lean::cnstr_set(x_481, 2, x_480);
x_482 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_476, x_481);
x_483 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_482);
x_26 = x_483;
goto lbl_27;
}
else
{
obj* x_485; uint8 x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; 
lean::dec(x_28);
x_485 = lean::cnstr_get(x_471, 0);
x_487 = lean::cnstr_get_scalar<uint8>(x_471, sizeof(void*)*1);
if (lean::is_exclusive(x_471)) {
 lean::cnstr_set(x_471, 0, lean::box(0));
 x_488 = x_471;
} else {
 lean::inc(x_485);
 lean::dec(x_471);
 x_488 = lean::box(0);
}
if (lean::is_scalar(x_488)) {
 x_489 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_489 = x_488;
}
lean::cnstr_set(x_489, 0, x_485);
lean::cnstr_set_scalar(x_489, sizeof(void*)*1, x_487);
x_490 = x_489;
x_491 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_490);
x_26 = x_491;
goto lbl_27;
}
}
}
else
{
obj* x_496; uint8 x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_18);
x_496 = lean::cnstr_get(x_20, 0);
x_498 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_499 = x_20;
} else {
 lean::inc(x_496);
 lean::dec(x_20);
 x_499 = lean::box(0);
}
if (lean::is_scalar(x_499)) {
 x_500 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_500 = x_499;
}
lean::cnstr_set(x_500, 0, x_496);
lean::cnstr_set_scalar(x_500, sizeof(void*)*1, x_498);
x_501 = x_500;
x_502 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_501);
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_502);
return x_503;
}
}
else
{
obj* x_506; uint8 x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; 
lean::dec(x_8);
lean::dec(x_0);
x_506 = lean::cnstr_get(x_11, 0);
x_508 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_509 = x_11;
} else {
 lean::inc(x_506);
 lean::dec(x_11);
 x_509 = lean::box(0);
}
if (lean::is_scalar(x_509)) {
 x_510 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_510 = x_509;
}
lean::cnstr_set(x_510, 0, x_506);
lean::cnstr_set_scalar(x_510, sizeof(void*)*1, x_508);
x_511 = x_510;
x_512 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_511);
return x_512;
}
}
else
{
obj* x_514; uint8 x_516; obj* x_517; obj* x_518; obj* x_519; 
lean::dec(x_0);
x_514 = lean::cnstr_get(x_3, 0);
x_516 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_517 = x_3;
} else {
 lean::inc(x_514);
 lean::dec(x_3);
 x_517 = lean::box(0);
}
if (lean::is_scalar(x_517)) {
 x_518 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_518 = x_517;
}
lean::cnstr_set(x_518, 0, x_514);
lean::cnstr_set_scalar(x_518, sizeof(void*)*1, x_516);
x_519 = x_518;
return x_519;
}
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = l_lean_ir_parse__typed__assignment___lambda__1(x_0, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = l_lean_ir_parse__typed__assignment___lambda__2(x_0, x_4, x_5, x_3);
return x_6;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; usize x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox_size_t(x_3);
x_6 = l_lean_ir_parse__typed__assignment___lambda__3(x_0, x_4, x_2, x_5);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(14, 3, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_1);
x_5 = x_4;
return x_5;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(13, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__3(obj* x_0, uint16 x_1, uint16 x_2, usize x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_cnstr(6, 1, sizeof(size_t)*1 + 4);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_1);
x_5 = x_4;
lean::cnstr_set_scalar(x_5, sizeof(void*)*2 + 2, x_2);
x_6 = x_5;
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_3);
x_7 = x_6;
return x_7;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__5(obj* x_0, obj* x_1, uint16 x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(8, 2, 2);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_2);
x_4 = x_3;
return x_4;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(11, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("sarray");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("array");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("cnstr");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("call");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("get");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("apply");
return x_0;
}
}
obj* _init_l_lean_ir_parse__untyped__assignment___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("closure");
return x_0;
}
}
obj* l_lean_ir_parse__untyped__assignment(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_parse__typed__assignment___closed__3;
x_3 = l_lean_ir_symbol(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 lean::cnstr_set(x_3, 2, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_15 = l_lean_ir_parse__untyped__assignment___closed__7;
lean::inc(x_4);
x_17 = l_lean_ir_keyword(x_15, x_4);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_17, 1);
x_20 = lean::cnstr_get(x_17, 2);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_set(x_17, 1, lean::box(0));
 lean::cnstr_set(x_17, 2, lean::box(0));
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = l_lean_ir_parse__fnid(x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 2);
lean::inc(x_28);
lean::dec(x_23);
lean::inc(x_0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__6), 3, 2);
lean::closure_set(x_32, 0, x_0);
lean::closure_set(x_32, 1, x_24);
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_22)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_22;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_26);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_39; obj* x_41; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_36, 2);
lean::inc(x_41);
lean::dec(x_36);
x_11 = x_37;
x_12 = x_39;
x_13 = x_41;
goto lbl_14;
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_36, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_36, sizeof(void*)*1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_set(x_36, 0, lean::box(0));
 x_47 = x_36;
} else {
 lean::inc(x_44);
 lean::dec(x_36);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
x_9 = x_49;
goto lbl_10;
}
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_22);
x_51 = lean::cnstr_get(x_23, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_set(x_23, 0, lean::box(0));
 x_54 = x_23;
} else {
 lean::inc(x_51);
 lean::dec(x_23);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 2);
lean::inc(x_62);
lean::dec(x_57);
x_11 = x_58;
x_12 = x_60;
x_13 = x_62;
goto lbl_14;
}
else
{
obj* x_65; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_57, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_set(x_57, 0, lean::box(0));
 x_68 = x_57;
} else {
 lean::inc(x_65);
 lean::dec(x_57);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_67);
x_70 = x_69;
x_9 = x_70;
goto lbl_10;
}
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_17, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_74 = x_17;
} else {
 lean::inc(x_71);
 lean::dec(x_17);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
x_9 = x_76;
goto lbl_10;
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_80; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; uint8 x_86; 
x_81 = lean::cnstr_get(x_9, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_83 == 0)
{
obj* x_89; obj* x_91; 
lean::dec(x_9);
x_89 = l_lean_ir_parse__untyped__assignment___closed__6;
lean::inc(x_4);
x_91 = l_lean_ir_keyword(x_89, x_4);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_97; 
x_92 = lean::cnstr_get(x_91, 1);
x_94 = lean::cnstr_get(x_91, 2);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_set(x_91, 1, lean::box(0));
 lean::cnstr_set(x_91, 2, lean::box(0));
 x_96 = x_91;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_91);
 x_96 = lean::box(0);
}
x_97 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(x_92);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_97, 2);
lean::inc(x_102);
lean::dec(x_97);
lean::inc(x_0);
x_106 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_106, 0, x_0);
lean::cnstr_set(x_106, 1, x_98);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_96)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_96;
}
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_100);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_115; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_114 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_110);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_114);
return x_115;
}
else
{
obj* x_116; uint8 x_118; 
x_116 = lean::cnstr_get(x_110, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
x_84 = x_110;
x_85 = x_116;
x_86 = x_118;
goto lbl_87;
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_96);
x_120 = lean::cnstr_get(x_97, 0);
x_122 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_set(x_97, 0, lean::box(0));
 x_123 = x_97;
} else {
 lean::inc(x_120);
 lean::dec(x_97);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_122);
x_125 = x_124;
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_130; obj* x_131; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_130 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_126);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_130);
return x_131;
}
else
{
obj* x_132; uint8 x_134; 
x_132 = lean::cnstr_get(x_126, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
x_84 = x_126;
x_85 = x_132;
x_86 = x_134;
goto lbl_87;
}
}
}
else
{
obj* x_135; uint8 x_137; obj* x_138; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_91, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_set(x_91, 0, lean::box(0));
 x_138 = x_91;
} else {
 lean::inc(x_135);
 lean::dec(x_91);
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
x_84 = x_141;
x_85 = x_135;
x_86 = x_137;
goto lbl_87;
}
}
else
{
obj* x_146; 
lean::dec(x_81);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_146;
}
lbl_87:
{
obj* x_147; obj* x_148; uint8 x_149; obj* x_151; obj* x_152; obj* x_153; 
if (x_86 == 0)
{
obj* x_156; obj* x_158; 
lean::dec(x_84);
x_156 = l_lean_ir_parse__untyped__assignment___closed__5;
lean::inc(x_4);
x_158 = l_lean_ir_keyword(x_156, x_4);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; 
x_159 = lean::cnstr_get(x_158, 1);
x_161 = lean::cnstr_get(x_158, 2);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_set(x_158, 1, lean::box(0));
 lean::cnstr_set(x_158, 2, lean::box(0));
 x_163 = x_158;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_158);
 x_163 = lean::box(0);
}
x_164 = l_lean_ir_parse__var(x_159);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_167; obj* x_169; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 2);
lean::inc(x_169);
lean::dec(x_164);
lean::inc(x_0);
x_173 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__5___boxed), 3, 2);
lean::closure_set(x_173, 0, x_0);
lean::closure_set(x_173, 1, x_165);
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_163)) {
 x_175 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_175 = x_163;
}
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set(x_175, 1, x_167);
lean::cnstr_set(x_175, 2, x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_175);
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_176);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_180; obj* x_182; 
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_177, 1);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_177, 2);
lean::inc(x_182);
lean::dec(x_177);
x_151 = x_178;
x_152 = x_180;
x_153 = x_182;
goto lbl_154;
}
else
{
obj* x_185; uint8 x_187; obj* x_188; obj* x_190; obj* x_191; 
x_185 = lean::cnstr_get(x_177, 0);
x_187 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*1);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_set(x_177, 0, lean::box(0));
 x_188 = x_177;
} else {
 lean::inc(x_185);
 lean::dec(x_177);
 x_188 = lean::box(0);
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
x_147 = x_191;
x_148 = x_185;
x_149 = x_187;
goto lbl_150;
}
}
else
{
obj* x_193; uint8 x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_163);
x_193 = lean::cnstr_get(x_164, 0);
x_195 = lean::cnstr_get_scalar<uint8>(x_164, sizeof(void*)*1);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_set(x_164, 0, lean::box(0));
 x_196 = x_164;
} else {
 lean::inc(x_193);
 lean::dec(x_164);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_193);
lean::cnstr_set_scalar(x_197, sizeof(void*)*1, x_195);
x_198 = x_197;
x_199 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_198);
if (lean::obj_tag(x_199) == 0)
{
obj* x_200; obj* x_202; obj* x_204; 
x_200 = lean::cnstr_get(x_199, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_199, 2);
lean::inc(x_204);
lean::dec(x_199);
x_151 = x_200;
x_152 = x_202;
x_153 = x_204;
goto lbl_154;
}
else
{
obj* x_207; uint8 x_209; obj* x_210; obj* x_212; obj* x_213; 
x_207 = lean::cnstr_get(x_199, 0);
x_209 = lean::cnstr_get_scalar<uint8>(x_199, sizeof(void*)*1);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_set(x_199, 0, lean::box(0));
 x_210 = x_199;
} else {
 lean::inc(x_207);
 lean::dec(x_199);
 x_210 = lean::box(0);
}
lean::inc(x_207);
if (lean::is_scalar(x_210)) {
 x_212 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_212 = x_210;
}
lean::cnstr_set(x_212, 0, x_207);
lean::cnstr_set_scalar(x_212, sizeof(void*)*1, x_209);
x_213 = x_212;
x_147 = x_213;
x_148 = x_207;
x_149 = x_209;
goto lbl_150;
}
}
}
else
{
obj* x_214; uint8 x_216; obj* x_217; obj* x_219; obj* x_220; 
x_214 = lean::cnstr_get(x_158, 0);
x_216 = lean::cnstr_get_scalar<uint8>(x_158, sizeof(void*)*1);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_set(x_158, 0, lean::box(0));
 x_217 = x_158;
} else {
 lean::inc(x_214);
 lean::dec(x_158);
 x_217 = lean::box(0);
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
x_147 = x_220;
x_148 = x_214;
x_149 = x_216;
goto lbl_150;
}
}
else
{
obj* x_225; obj* x_226; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_85);
x_225 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_84);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_225);
return x_226;
}
lbl_150:
{
obj* x_227; obj* x_228; uint8 x_229; obj* x_231; obj* x_232; obj* x_233; 
if (x_149 == 0)
{
obj* x_236; obj* x_238; 
lean::dec(x_147);
x_236 = l_lean_ir_parse__untyped__assignment___closed__4;
lean::inc(x_4);
x_238 = l_lean_ir_keyword(x_236, x_4);
if (lean::obj_tag(x_238) == 0)
{
obj* x_239; obj* x_241; obj* x_243; obj* x_244; 
x_239 = lean::cnstr_get(x_238, 1);
x_241 = lean::cnstr_get(x_238, 2);
if (lean::is_exclusive(x_238)) {
 lean::cnstr_release(x_238, 0);
 lean::cnstr_set(x_238, 1, lean::box(0));
 lean::cnstr_set(x_238, 2, lean::box(0));
 x_243 = x_238;
} else {
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_238);
 x_243 = lean::box(0);
}
x_244 = l_lean_ir_parse__fnid(x_239);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_249; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_244, 2);
lean::inc(x_249);
lean::dec(x_244);
lean::inc(x_0);
x_253 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__4), 3, 2);
lean::closure_set(x_253, 0, x_0);
lean::closure_set(x_253, 1, x_245);
x_254 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_243)) {
 x_255 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_255 = x_243;
}
lean::cnstr_set(x_255, 0, x_253);
lean::cnstr_set(x_255, 1, x_247);
lean::cnstr_set(x_255, 2, x_254);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_249, x_255);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_256);
if (lean::obj_tag(x_257) == 0)
{
obj* x_258; obj* x_260; obj* x_262; 
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_257, 2);
lean::inc(x_262);
lean::dec(x_257);
x_231 = x_258;
x_232 = x_260;
x_233 = x_262;
goto lbl_234;
}
else
{
obj* x_265; uint8 x_267; obj* x_268; obj* x_270; obj* x_271; 
x_265 = lean::cnstr_get(x_257, 0);
x_267 = lean::cnstr_get_scalar<uint8>(x_257, sizeof(void*)*1);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_set(x_257, 0, lean::box(0));
 x_268 = x_257;
} else {
 lean::inc(x_265);
 lean::dec(x_257);
 x_268 = lean::box(0);
}
lean::inc(x_265);
if (lean::is_scalar(x_268)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_268;
}
lean::cnstr_set(x_270, 0, x_265);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_267);
x_271 = x_270;
x_227 = x_271;
x_228 = x_265;
x_229 = x_267;
goto lbl_230;
}
}
else
{
obj* x_273; uint8 x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
lean::dec(x_243);
x_273 = lean::cnstr_get(x_244, 0);
x_275 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
if (lean::is_exclusive(x_244)) {
 lean::cnstr_set(x_244, 0, lean::box(0));
 x_276 = x_244;
} else {
 lean::inc(x_273);
 lean::dec(x_244);
 x_276 = lean::box(0);
}
if (lean::is_scalar(x_276)) {
 x_277 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_277 = x_276;
}
lean::cnstr_set(x_277, 0, x_273);
lean::cnstr_set_scalar(x_277, sizeof(void*)*1, x_275);
x_278 = x_277;
x_279 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_278);
if (lean::obj_tag(x_279) == 0)
{
obj* x_280; obj* x_282; obj* x_284; 
x_280 = lean::cnstr_get(x_279, 0);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_279, 1);
lean::inc(x_282);
x_284 = lean::cnstr_get(x_279, 2);
lean::inc(x_284);
lean::dec(x_279);
x_231 = x_280;
x_232 = x_282;
x_233 = x_284;
goto lbl_234;
}
else
{
obj* x_287; uint8 x_289; obj* x_290; obj* x_292; obj* x_293; 
x_287 = lean::cnstr_get(x_279, 0);
x_289 = lean::cnstr_get_scalar<uint8>(x_279, sizeof(void*)*1);
if (lean::is_exclusive(x_279)) {
 lean::cnstr_set(x_279, 0, lean::box(0));
 x_290 = x_279;
} else {
 lean::inc(x_287);
 lean::dec(x_279);
 x_290 = lean::box(0);
}
lean::inc(x_287);
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_287);
lean::cnstr_set_scalar(x_292, sizeof(void*)*1, x_289);
x_293 = x_292;
x_227 = x_293;
x_228 = x_287;
x_229 = x_289;
goto lbl_230;
}
}
}
else
{
obj* x_294; uint8 x_296; obj* x_297; obj* x_299; obj* x_300; 
x_294 = lean::cnstr_get(x_238, 0);
x_296 = lean::cnstr_get_scalar<uint8>(x_238, sizeof(void*)*1);
if (lean::is_exclusive(x_238)) {
 lean::cnstr_set(x_238, 0, lean::box(0));
 x_297 = x_238;
} else {
 lean::inc(x_294);
 lean::dec(x_238);
 x_297 = lean::box(0);
}
lean::inc(x_294);
if (lean::is_scalar(x_297)) {
 x_299 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_299 = x_297;
}
lean::cnstr_set(x_299, 0, x_294);
lean::cnstr_set_scalar(x_299, sizeof(void*)*1, x_296);
x_300 = x_299;
x_227 = x_300;
x_228 = x_294;
x_229 = x_296;
goto lbl_230;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; 
lean::dec(x_148);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_305 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_147);
x_306 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_305);
x_307 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_306);
return x_307;
}
lbl_230:
{
obj* x_308; obj* x_309; uint8 x_310; obj* x_312; obj* x_313; obj* x_314; obj* x_316; obj* x_317; obj* x_318; 
if (x_229 == 0)
{
obj* x_321; obj* x_323; 
lean::dec(x_227);
x_321 = l_lean_ir_parse__untyped__assignment___closed__3;
lean::inc(x_4);
x_323 = l_lean_ir_keyword(x_321, x_4);
if (lean::obj_tag(x_323) == 0)
{
obj* x_324; obj* x_326; obj* x_328; obj* x_329; 
x_324 = lean::cnstr_get(x_323, 1);
x_326 = lean::cnstr_get(x_323, 2);
if (lean::is_exclusive(x_323)) {
 lean::cnstr_release(x_323, 0);
 lean::cnstr_set(x_323, 1, lean::box(0));
 lean::cnstr_set(x_323, 2, lean::box(0));
 x_328 = x_323;
} else {
 lean::inc(x_324);
 lean::inc(x_326);
 lean::dec(x_323);
 x_328 = lean::box(0);
}
x_329 = l_lean_ir_parse__uint16(x_324);
if (lean::obj_tag(x_329) == 0)
{
obj* x_330; obj* x_332; obj* x_334; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_329, 2);
lean::inc(x_334);
lean::dec(x_329);
lean::inc(x_0);
x_338 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__3___boxed), 4, 2);
lean::closure_set(x_338, 0, x_0);
lean::closure_set(x_338, 1, x_330);
x_339 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_328)) {
 x_340 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_340 = x_328;
}
lean::cnstr_set(x_340, 0, x_338);
lean::cnstr_set(x_340, 1, x_332);
lean::cnstr_set(x_340, 2, x_339);
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_334, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_326, x_341);
if (lean::obj_tag(x_342) == 0)
{
obj* x_343; obj* x_345; obj* x_347; 
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_342, 1);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_342, 2);
lean::inc(x_347);
lean::dec(x_342);
x_316 = x_343;
x_317 = x_345;
x_318 = x_347;
goto lbl_319;
}
else
{
obj* x_350; uint8 x_352; obj* x_353; obj* x_355; obj* x_356; 
x_350 = lean::cnstr_get(x_342, 0);
x_352 = lean::cnstr_get_scalar<uint8>(x_342, sizeof(void*)*1);
if (lean::is_exclusive(x_342)) {
 lean::cnstr_set(x_342, 0, lean::box(0));
 x_353 = x_342;
} else {
 lean::inc(x_350);
 lean::dec(x_342);
 x_353 = lean::box(0);
}
lean::inc(x_350);
if (lean::is_scalar(x_353)) {
 x_355 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_355 = x_353;
}
lean::cnstr_set(x_355, 0, x_350);
lean::cnstr_set_scalar(x_355, sizeof(void*)*1, x_352);
x_356 = x_355;
x_308 = x_356;
x_309 = x_350;
x_310 = x_352;
goto lbl_311;
}
}
else
{
obj* x_358; uint8 x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
lean::dec(x_328);
x_358 = lean::cnstr_get(x_329, 0);
x_360 = lean::cnstr_get_scalar<uint8>(x_329, sizeof(void*)*1);
if (lean::is_exclusive(x_329)) {
 lean::cnstr_set(x_329, 0, lean::box(0));
 x_361 = x_329;
} else {
 lean::inc(x_358);
 lean::dec(x_329);
 x_361 = lean::box(0);
}
if (lean::is_scalar(x_361)) {
 x_362 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_362 = x_361;
}
lean::cnstr_set(x_362, 0, x_358);
lean::cnstr_set_scalar(x_362, sizeof(void*)*1, x_360);
x_363 = x_362;
x_364 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_326, x_363);
if (lean::obj_tag(x_364) == 0)
{
obj* x_365; obj* x_367; obj* x_369; 
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
x_367 = lean::cnstr_get(x_364, 1);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_364, 2);
lean::inc(x_369);
lean::dec(x_364);
x_316 = x_365;
x_317 = x_367;
x_318 = x_369;
goto lbl_319;
}
else
{
obj* x_372; uint8 x_374; obj* x_375; obj* x_377; obj* x_378; 
x_372 = lean::cnstr_get(x_364, 0);
x_374 = lean::cnstr_get_scalar<uint8>(x_364, sizeof(void*)*1);
if (lean::is_exclusive(x_364)) {
 lean::cnstr_set(x_364, 0, lean::box(0));
 x_375 = x_364;
} else {
 lean::inc(x_372);
 lean::dec(x_364);
 x_375 = lean::box(0);
}
lean::inc(x_372);
if (lean::is_scalar(x_375)) {
 x_377 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_377 = x_375;
}
lean::cnstr_set(x_377, 0, x_372);
lean::cnstr_set_scalar(x_377, sizeof(void*)*1, x_374);
x_378 = x_377;
x_308 = x_378;
x_309 = x_372;
x_310 = x_374;
goto lbl_311;
}
}
}
else
{
obj* x_379; uint8 x_381; obj* x_382; obj* x_384; obj* x_385; 
x_379 = lean::cnstr_get(x_323, 0);
x_381 = lean::cnstr_get_scalar<uint8>(x_323, sizeof(void*)*1);
if (lean::is_exclusive(x_323)) {
 lean::cnstr_set(x_323, 0, lean::box(0));
 x_382 = x_323;
} else {
 lean::inc(x_379);
 lean::dec(x_323);
 x_382 = lean::box(0);
}
lean::inc(x_379);
if (lean::is_scalar(x_382)) {
 x_384 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_384 = x_382;
}
lean::cnstr_set(x_384, 0, x_379);
lean::cnstr_set_scalar(x_384, sizeof(void*)*1, x_381);
x_385 = x_384;
x_308 = x_385;
x_309 = x_379;
x_310 = x_381;
goto lbl_311;
}
}
else
{
obj* x_390; obj* x_391; obj* x_392; obj* x_393; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_228);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_227);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_390);
x_392 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_391);
x_393 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_392);
return x_393;
}
lbl_311:
{
obj* x_394; obj* x_395; uint8 x_396; obj* x_398; obj* x_399; obj* x_400; 
if (x_310 == 0)
{
obj* x_403; obj* x_405; 
lean::dec(x_308);
x_403 = l_lean_ir_parse__untyped__assignment___closed__2;
lean::inc(x_4);
x_405 = l_lean_ir_keyword(x_403, x_4);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_408; obj* x_410; obj* x_411; 
x_406 = lean::cnstr_get(x_405, 1);
x_408 = lean::cnstr_get(x_405, 2);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_set(x_405, 1, lean::box(0));
 lean::cnstr_set(x_405, 2, lean::box(0));
 x_410 = x_405;
} else {
 lean::inc(x_406);
 lean::inc(x_408);
 lean::dec(x_405);
 x_410 = lean::box(0);
}
x_411 = l_lean_ir_parse__var(x_406);
if (lean::obj_tag(x_411) == 0)
{
obj* x_412; obj* x_414; obj* x_416; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
x_412 = lean::cnstr_get(x_411, 0);
lean::inc(x_412);
x_414 = lean::cnstr_get(x_411, 1);
lean::inc(x_414);
x_416 = lean::cnstr_get(x_411, 2);
lean::inc(x_416);
lean::dec(x_411);
lean::inc(x_0);
x_420 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__2), 3, 2);
lean::closure_set(x_420, 0, x_0);
lean::closure_set(x_420, 1, x_412);
x_421 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_410)) {
 x_422 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_422 = x_410;
}
lean::cnstr_set(x_422, 0, x_420);
lean::cnstr_set(x_422, 1, x_414);
lean::cnstr_set(x_422, 2, x_421);
x_423 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_416, x_422);
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_408, x_423);
if (lean::obj_tag(x_424) == 0)
{
obj* x_425; obj* x_427; obj* x_429; 
x_425 = lean::cnstr_get(x_424, 0);
lean::inc(x_425);
x_427 = lean::cnstr_get(x_424, 1);
lean::inc(x_427);
x_429 = lean::cnstr_get(x_424, 2);
lean::inc(x_429);
lean::dec(x_424);
x_398 = x_425;
x_399 = x_427;
x_400 = x_429;
goto lbl_401;
}
else
{
obj* x_432; uint8 x_434; obj* x_435; obj* x_437; obj* x_438; 
x_432 = lean::cnstr_get(x_424, 0);
x_434 = lean::cnstr_get_scalar<uint8>(x_424, sizeof(void*)*1);
if (lean::is_exclusive(x_424)) {
 lean::cnstr_set(x_424, 0, lean::box(0));
 x_435 = x_424;
} else {
 lean::inc(x_432);
 lean::dec(x_424);
 x_435 = lean::box(0);
}
lean::inc(x_432);
if (lean::is_scalar(x_435)) {
 x_437 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_437 = x_435;
}
lean::cnstr_set(x_437, 0, x_432);
lean::cnstr_set_scalar(x_437, sizeof(void*)*1, x_434);
x_438 = x_437;
x_394 = x_438;
x_395 = x_432;
x_396 = x_434;
goto lbl_397;
}
}
else
{
obj* x_440; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; 
lean::dec(x_410);
x_440 = lean::cnstr_get(x_411, 0);
x_442 = lean::cnstr_get_scalar<uint8>(x_411, sizeof(void*)*1);
if (lean::is_exclusive(x_411)) {
 lean::cnstr_set(x_411, 0, lean::box(0));
 x_443 = x_411;
} else {
 lean::inc(x_440);
 lean::dec(x_411);
 x_443 = lean::box(0);
}
if (lean::is_scalar(x_443)) {
 x_444 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_444 = x_443;
}
lean::cnstr_set(x_444, 0, x_440);
lean::cnstr_set_scalar(x_444, sizeof(void*)*1, x_442);
x_445 = x_444;
x_446 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_408, x_445);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_449; obj* x_451; 
x_447 = lean::cnstr_get(x_446, 0);
lean::inc(x_447);
x_449 = lean::cnstr_get(x_446, 1);
lean::inc(x_449);
x_451 = lean::cnstr_get(x_446, 2);
lean::inc(x_451);
lean::dec(x_446);
x_398 = x_447;
x_399 = x_449;
x_400 = x_451;
goto lbl_401;
}
else
{
obj* x_454; uint8 x_456; obj* x_457; obj* x_459; obj* x_460; 
x_454 = lean::cnstr_get(x_446, 0);
x_456 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*1);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_set(x_446, 0, lean::box(0));
 x_457 = x_446;
} else {
 lean::inc(x_454);
 lean::dec(x_446);
 x_457 = lean::box(0);
}
lean::inc(x_454);
if (lean::is_scalar(x_457)) {
 x_459 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_459 = x_457;
}
lean::cnstr_set(x_459, 0, x_454);
lean::cnstr_set_scalar(x_459, sizeof(void*)*1, x_456);
x_460 = x_459;
x_394 = x_460;
x_395 = x_454;
x_396 = x_456;
goto lbl_397;
}
}
}
else
{
obj* x_461; uint8 x_463; obj* x_464; obj* x_466; obj* x_467; 
x_461 = lean::cnstr_get(x_405, 0);
x_463 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*1);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_set(x_405, 0, lean::box(0));
 x_464 = x_405;
} else {
 lean::inc(x_461);
 lean::dec(x_405);
 x_464 = lean::box(0);
}
lean::inc(x_461);
if (lean::is_scalar(x_464)) {
 x_466 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_466 = x_464;
}
lean::cnstr_set(x_466, 0, x_461);
lean::cnstr_set_scalar(x_466, sizeof(void*)*1, x_463);
x_467 = x_466;
x_394 = x_467;
x_395 = x_461;
x_396 = x_463;
goto lbl_397;
}
}
else
{
obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_309);
x_472 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_308);
x_473 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_472);
x_474 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_473);
x_475 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_474);
x_476 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_475);
return x_476;
}
lbl_397:
{
obj* x_477; obj* x_478; obj* x_479; obj* x_481; obj* x_482; obj* x_483; 
if (x_396 == 0)
{
obj* x_486; obj* x_487; 
lean::dec(x_394);
x_486 = l_lean_ir_parse__untyped__assignment___closed__1;
x_487 = l_lean_ir_keyword(x_486, x_4);
if (lean::obj_tag(x_487) == 0)
{
obj* x_488; obj* x_490; obj* x_492; obj* x_493; obj* x_494; obj* x_495; 
x_488 = lean::cnstr_get(x_487, 1);
x_490 = lean::cnstr_get(x_487, 2);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 lean::cnstr_set(x_487, 1, lean::box(0));
 lean::cnstr_set(x_487, 2, lean::box(0));
 x_492 = x_487;
} else {
 lean::inc(x_488);
 lean::inc(x_490);
 lean::dec(x_487);
 x_492 = lean::box(0);
}
x_493 = l_lean_ir_parse__typed__assignment___closed__2;
x_494 = l_lean_ir_str2type;
x_495 = l_lean_ir_parse__key2val___main___rarg(x_493, x_494, x_488);
if (lean::obj_tag(x_495) == 0)
{
obj* x_496; obj* x_498; obj* x_500; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; 
x_496 = lean::cnstr_get(x_495, 0);
lean::inc(x_496);
x_498 = lean::cnstr_get(x_495, 1);
lean::inc(x_498);
x_500 = lean::cnstr_get(x_495, 2);
lean::inc(x_500);
lean::dec(x_495);
x_503 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__1___boxed), 4, 2);
lean::closure_set(x_503, 0, x_0);
lean::closure_set(x_503, 1, x_496);
x_504 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_492)) {
 x_505 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_505 = x_492;
}
lean::cnstr_set(x_505, 0, x_503);
lean::cnstr_set(x_505, 1, x_498);
lean::cnstr_set(x_505, 2, x_504);
x_506 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_500, x_505);
x_507 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_490, x_506);
if (lean::obj_tag(x_507) == 0)
{
obj* x_508; obj* x_510; obj* x_512; 
x_508 = lean::cnstr_get(x_507, 0);
lean::inc(x_508);
x_510 = lean::cnstr_get(x_507, 1);
lean::inc(x_510);
x_512 = lean::cnstr_get(x_507, 2);
lean::inc(x_512);
lean::dec(x_507);
x_481 = x_508;
x_482 = x_510;
x_483 = x_512;
goto lbl_484;
}
else
{
obj* x_516; uint8 x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_8);
x_516 = lean::cnstr_get(x_507, 0);
x_518 = lean::cnstr_get_scalar<uint8>(x_507, sizeof(void*)*1);
if (lean::is_exclusive(x_507)) {
 lean::cnstr_set(x_507, 0, lean::box(0));
 x_519 = x_507;
} else {
 lean::inc(x_516);
 lean::dec(x_507);
 x_519 = lean::box(0);
}
if (lean::is_scalar(x_519)) {
 x_520 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_520 = x_519;
}
lean::cnstr_set(x_520, 0, x_516);
lean::cnstr_set_scalar(x_520, sizeof(void*)*1, x_518);
x_521 = x_520;
x_522 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_521);
x_523 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_522);
x_524 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_523);
x_525 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_524);
x_526 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_525);
x_527 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_526);
x_528 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_527);
return x_528;
}
}
else
{
obj* x_531; uint8 x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; 
lean::dec(x_0);
lean::dec(x_492);
x_531 = lean::cnstr_get(x_495, 0);
x_533 = lean::cnstr_get_scalar<uint8>(x_495, sizeof(void*)*1);
if (lean::is_exclusive(x_495)) {
 lean::cnstr_set(x_495, 0, lean::box(0));
 x_534 = x_495;
} else {
 lean::inc(x_531);
 lean::dec(x_495);
 x_534 = lean::box(0);
}
if (lean::is_scalar(x_534)) {
 x_535 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_535 = x_534;
}
lean::cnstr_set(x_535, 0, x_531);
lean::cnstr_set_scalar(x_535, sizeof(void*)*1, x_533);
x_536 = x_535;
x_537 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_490, x_536);
if (lean::obj_tag(x_537) == 0)
{
obj* x_538; obj* x_540; obj* x_542; 
x_538 = lean::cnstr_get(x_537, 0);
lean::inc(x_538);
x_540 = lean::cnstr_get(x_537, 1);
lean::inc(x_540);
x_542 = lean::cnstr_get(x_537, 2);
lean::inc(x_542);
lean::dec(x_537);
x_481 = x_538;
x_482 = x_540;
x_483 = x_542;
goto lbl_484;
}
else
{
obj* x_546; uint8 x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; 
lean::dec(x_8);
x_546 = lean::cnstr_get(x_537, 0);
x_548 = lean::cnstr_get_scalar<uint8>(x_537, sizeof(void*)*1);
if (lean::is_exclusive(x_537)) {
 lean::cnstr_set(x_537, 0, lean::box(0));
 x_549 = x_537;
} else {
 lean::inc(x_546);
 lean::dec(x_537);
 x_549 = lean::box(0);
}
if (lean::is_scalar(x_549)) {
 x_550 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_550 = x_549;
}
lean::cnstr_set(x_550, 0, x_546);
lean::cnstr_set_scalar(x_550, sizeof(void*)*1, x_548);
x_551 = x_550;
x_552 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_551);
x_553 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_552);
x_554 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_553);
x_555 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_554);
x_556 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_555);
x_557 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_556);
x_558 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_557);
return x_558;
}
}
}
else
{
obj* x_561; uint8 x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; 
lean::dec(x_8);
lean::dec(x_0);
x_561 = lean::cnstr_get(x_487, 0);
x_563 = lean::cnstr_get_scalar<uint8>(x_487, sizeof(void*)*1);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_set(x_487, 0, lean::box(0));
 x_564 = x_487;
} else {
 lean::inc(x_561);
 lean::dec(x_487);
 x_564 = lean::box(0);
}
if (lean::is_scalar(x_564)) {
 x_565 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_565 = x_564;
}
lean::cnstr_set(x_565, 0, x_561);
lean::cnstr_set_scalar(x_565, sizeof(void*)*1, x_563);
x_566 = x_565;
x_567 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_566);
x_568 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_567);
x_569 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_568);
x_570 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_569);
x_571 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_570);
x_572 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_571);
x_573 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_572);
return x_573;
}
}
else
{
obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; 
lean::dec(x_395);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_394);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_578);
x_580 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_579);
x_581 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_580);
x_582 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_581);
x_583 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_582);
return x_583;
}
lbl_480:
{
obj* x_584; 
x_584 = l_lean_ir_parse__var(x_478);
if (lean::obj_tag(x_584) == 0)
{
obj* x_585; obj* x_587; obj* x_589; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; 
x_585 = lean::cnstr_get(x_584, 0);
lean::inc(x_585);
x_587 = lean::cnstr_get(x_584, 1);
lean::inc(x_587);
x_589 = lean::cnstr_get(x_584, 2);
lean::inc(x_589);
lean::dec(x_584);
x_592 = lean::apply_1(x_477, x_585);
x_593 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_594 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_594 = x_8;
}
lean::cnstr_set(x_594, 0, x_592);
lean::cnstr_set(x_594, 1, x_587);
lean::cnstr_set(x_594, 2, x_593);
x_595 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_589, x_594);
x_596 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_479, x_595);
x_597 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_596);
x_598 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_597);
x_599 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_598);
x_600 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_599);
x_601 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_600);
x_602 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_601);
x_603 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_602);
return x_603;
}
else
{
obj* x_606; uint8 x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; 
lean::dec(x_477);
lean::dec(x_8);
x_606 = lean::cnstr_get(x_584, 0);
x_608 = lean::cnstr_get_scalar<uint8>(x_584, sizeof(void*)*1);
if (lean::is_exclusive(x_584)) {
 lean::cnstr_set(x_584, 0, lean::box(0));
 x_609 = x_584;
} else {
 lean::inc(x_606);
 lean::dec(x_584);
 x_609 = lean::box(0);
}
if (lean::is_scalar(x_609)) {
 x_610 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_610 = x_609;
}
lean::cnstr_set(x_610, 0, x_606);
lean::cnstr_set_scalar(x_610, sizeof(void*)*1, x_608);
x_611 = x_610;
x_612 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_479, x_611);
x_613 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_612);
x_614 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_613);
x_615 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_614);
x_616 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_615);
x_617 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_616);
x_618 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_617);
x_619 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_618);
return x_619;
}
}
lbl_484:
{
obj* x_620; 
x_620 = l_lean_ir_parse__var(x_482);
if (lean::obj_tag(x_620) == 0)
{
obj* x_621; obj* x_623; obj* x_625; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; 
x_621 = lean::cnstr_get(x_620, 0);
x_623 = lean::cnstr_get(x_620, 1);
x_625 = lean::cnstr_get(x_620, 2);
if (lean::is_exclusive(x_620)) {
 lean::cnstr_set(x_620, 0, lean::box(0));
 lean::cnstr_set(x_620, 1, lean::box(0));
 lean::cnstr_set(x_620, 2, lean::box(0));
 x_627 = x_620;
} else {
 lean::inc(x_621);
 lean::inc(x_623);
 lean::inc(x_625);
 lean::dec(x_620);
 x_627 = lean::box(0);
}
x_628 = lean::apply_1(x_481, x_621);
x_629 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_627)) {
 x_630 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_630 = x_627;
}
lean::cnstr_set(x_630, 0, x_628);
lean::cnstr_set(x_630, 1, x_623);
lean::cnstr_set(x_630, 2, x_629);
x_631 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_625, x_630);
x_632 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_483, x_631);
if (lean::obj_tag(x_632) == 0)
{
obj* x_633; obj* x_635; obj* x_637; 
x_633 = lean::cnstr_get(x_632, 0);
lean::inc(x_633);
x_635 = lean::cnstr_get(x_632, 1);
lean::inc(x_635);
x_637 = lean::cnstr_get(x_632, 2);
lean::inc(x_637);
lean::dec(x_632);
x_477 = x_633;
x_478 = x_635;
x_479 = x_637;
goto lbl_480;
}
else
{
obj* x_641; uint8 x_643; obj* x_644; obj* x_645; obj* x_646; obj* x_647; obj* x_648; obj* x_649; obj* x_650; obj* x_651; obj* x_652; obj* x_653; 
lean::dec(x_8);
x_641 = lean::cnstr_get(x_632, 0);
x_643 = lean::cnstr_get_scalar<uint8>(x_632, sizeof(void*)*1);
if (lean::is_exclusive(x_632)) {
 lean::cnstr_set(x_632, 0, lean::box(0));
 x_644 = x_632;
} else {
 lean::inc(x_641);
 lean::dec(x_632);
 x_644 = lean::box(0);
}
if (lean::is_scalar(x_644)) {
 x_645 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_645 = x_644;
}
lean::cnstr_set(x_645, 0, x_641);
lean::cnstr_set_scalar(x_645, sizeof(void*)*1, x_643);
x_646 = x_645;
x_647 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_646);
x_648 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_647);
x_649 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_648);
x_650 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_649);
x_651 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_650);
x_652 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_651);
x_653 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_652);
return x_653;
}
}
else
{
obj* x_655; uint8 x_657; obj* x_658; obj* x_659; obj* x_660; obj* x_661; 
lean::dec(x_481);
x_655 = lean::cnstr_get(x_620, 0);
x_657 = lean::cnstr_get_scalar<uint8>(x_620, sizeof(void*)*1);
if (lean::is_exclusive(x_620)) {
 lean::cnstr_set(x_620, 0, lean::box(0));
 x_658 = x_620;
} else {
 lean::inc(x_655);
 lean::dec(x_620);
 x_658 = lean::box(0);
}
if (lean::is_scalar(x_658)) {
 x_659 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_659 = x_658;
}
lean::cnstr_set(x_659, 0, x_655);
lean::cnstr_set_scalar(x_659, sizeof(void*)*1, x_657);
x_660 = x_659;
x_661 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_483, x_660);
if (lean::obj_tag(x_661) == 0)
{
obj* x_662; obj* x_664; obj* x_666; 
x_662 = lean::cnstr_get(x_661, 0);
lean::inc(x_662);
x_664 = lean::cnstr_get(x_661, 1);
lean::inc(x_664);
x_666 = lean::cnstr_get(x_661, 2);
lean::inc(x_666);
lean::dec(x_661);
x_477 = x_662;
x_478 = x_664;
x_479 = x_666;
goto lbl_480;
}
else
{
obj* x_670; uint8 x_672; obj* x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; obj* x_682; 
lean::dec(x_8);
x_670 = lean::cnstr_get(x_661, 0);
x_672 = lean::cnstr_get_scalar<uint8>(x_661, sizeof(void*)*1);
if (lean::is_exclusive(x_661)) {
 lean::cnstr_set(x_661, 0, lean::box(0));
 x_673 = x_661;
} else {
 lean::inc(x_670);
 lean::dec(x_661);
 x_673 = lean::box(0);
}
if (lean::is_scalar(x_673)) {
 x_674 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_674 = x_673;
}
lean::cnstr_set(x_674, 0, x_670);
lean::cnstr_set_scalar(x_674, sizeof(void*)*1, x_672);
x_675 = x_674;
x_676 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_395, x_675);
x_677 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_676);
x_678 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_677);
x_679 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_678);
x_680 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_679);
x_681 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_680);
x_682 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_681);
return x_682;
}
}
}
}
lbl_401:
{
obj* x_683; 
x_683 = l_lean_ir_parse__var(x_399);
if (lean::obj_tag(x_683) == 0)
{
obj* x_684; obj* x_686; obj* x_688; obj* x_690; obj* x_691; obj* x_692; obj* x_693; obj* x_694; obj* x_695; 
x_684 = lean::cnstr_get(x_683, 0);
x_686 = lean::cnstr_get(x_683, 1);
x_688 = lean::cnstr_get(x_683, 2);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_set(x_683, 0, lean::box(0));
 lean::cnstr_set(x_683, 1, lean::box(0));
 lean::cnstr_set(x_683, 2, lean::box(0));
 x_690 = x_683;
} else {
 lean::inc(x_684);
 lean::inc(x_686);
 lean::inc(x_688);
 lean::dec(x_683);
 x_690 = lean::box(0);
}
x_691 = lean::apply_1(x_398, x_684);
x_692 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_690)) {
 x_693 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_693 = x_690;
}
lean::cnstr_set(x_693, 0, x_691);
lean::cnstr_set(x_693, 1, x_686);
lean::cnstr_set(x_693, 2, x_692);
x_694 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_688, x_693);
x_695 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_400, x_694);
if (lean::obj_tag(x_695) == 0)
{
obj* x_699; obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_699 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_695);
x_700 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_699);
x_701 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_700);
x_702 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_701);
x_703 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_702);
x_704 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_703);
return x_704;
}
else
{
obj* x_705; uint8 x_707; 
x_705 = lean::cnstr_get(x_695, 0);
lean::inc(x_705);
x_707 = lean::cnstr_get_scalar<uint8>(x_695, sizeof(void*)*1);
x_394 = x_695;
x_395 = x_705;
x_396 = x_707;
goto lbl_397;
}
}
else
{
obj* x_709; uint8 x_711; obj* x_712; obj* x_713; obj* x_714; obj* x_715; 
lean::dec(x_398);
x_709 = lean::cnstr_get(x_683, 0);
x_711 = lean::cnstr_get_scalar<uint8>(x_683, sizeof(void*)*1);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_set(x_683, 0, lean::box(0));
 x_712 = x_683;
} else {
 lean::inc(x_709);
 lean::dec(x_683);
 x_712 = lean::box(0);
}
if (lean::is_scalar(x_712)) {
 x_713 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_713 = x_712;
}
lean::cnstr_set(x_713, 0, x_709);
lean::cnstr_set_scalar(x_713, sizeof(void*)*1, x_711);
x_714 = x_713;
x_715 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_400, x_714);
if (lean::obj_tag(x_715) == 0)
{
obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_719 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_309, x_715);
x_720 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_719);
x_721 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_720);
x_722 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_721);
x_723 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_722);
x_724 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_723);
return x_724;
}
else
{
obj* x_725; uint8 x_727; 
x_725 = lean::cnstr_get(x_715, 0);
lean::inc(x_725);
x_727 = lean::cnstr_get_scalar<uint8>(x_715, sizeof(void*)*1);
x_394 = x_715;
x_395 = x_725;
x_396 = x_727;
goto lbl_397;
}
}
}
}
lbl_315:
{
obj* x_728; 
x_728 = l_lean_ir_parse__usize(x_313);
if (lean::obj_tag(x_728) == 0)
{
obj* x_729; obj* x_731; obj* x_733; obj* x_735; obj* x_736; obj* x_737; obj* x_738; obj* x_739; obj* x_740; 
x_729 = lean::cnstr_get(x_728, 0);
x_731 = lean::cnstr_get(x_728, 1);
x_733 = lean::cnstr_get(x_728, 2);
if (lean::is_exclusive(x_728)) {
 lean::cnstr_set(x_728, 0, lean::box(0));
 lean::cnstr_set(x_728, 1, lean::box(0));
 lean::cnstr_set(x_728, 2, lean::box(0));
 x_735 = x_728;
} else {
 lean::inc(x_729);
 lean::inc(x_731);
 lean::inc(x_733);
 lean::dec(x_728);
 x_735 = lean::box(0);
}
x_736 = lean::apply_1(x_312, x_729);
x_737 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_735)) {
 x_738 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_738 = x_735;
}
lean::cnstr_set(x_738, 0, x_736);
lean::cnstr_set(x_738, 1, x_731);
lean::cnstr_set(x_738, 2, x_737);
x_739 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_733, x_738);
x_740 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_314, x_739);
if (lean::obj_tag(x_740) == 0)
{
obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_744 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_740);
x_745 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_744);
x_746 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_745);
x_747 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_746);
x_748 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_747);
return x_748;
}
else
{
obj* x_749; uint8 x_751; 
x_749 = lean::cnstr_get(x_740, 0);
lean::inc(x_749);
x_751 = lean::cnstr_get_scalar<uint8>(x_740, sizeof(void*)*1);
x_308 = x_740;
x_309 = x_749;
x_310 = x_751;
goto lbl_311;
}
}
else
{
obj* x_753; uint8 x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; 
lean::dec(x_312);
x_753 = lean::cnstr_get(x_728, 0);
x_755 = lean::cnstr_get_scalar<uint8>(x_728, sizeof(void*)*1);
if (lean::is_exclusive(x_728)) {
 lean::cnstr_set(x_728, 0, lean::box(0));
 x_756 = x_728;
} else {
 lean::inc(x_753);
 lean::dec(x_728);
 x_756 = lean::box(0);
}
if (lean::is_scalar(x_756)) {
 x_757 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_757 = x_756;
}
lean::cnstr_set(x_757, 0, x_753);
lean::cnstr_set_scalar(x_757, sizeof(void*)*1, x_755);
x_758 = x_757;
x_759 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_314, x_758);
if (lean::obj_tag(x_759) == 0)
{
obj* x_763; obj* x_764; obj* x_765; obj* x_766; obj* x_767; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_763 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_228, x_759);
x_764 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_763);
x_765 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_764);
x_766 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_765);
x_767 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_766);
return x_767;
}
else
{
obj* x_768; uint8 x_770; 
x_768 = lean::cnstr_get(x_759, 0);
lean::inc(x_768);
x_770 = lean::cnstr_get_scalar<uint8>(x_759, sizeof(void*)*1);
x_308 = x_759;
x_309 = x_768;
x_310 = x_770;
goto lbl_311;
}
}
}
lbl_319:
{
obj* x_771; 
x_771 = l_lean_ir_parse__uint16(x_317);
if (lean::obj_tag(x_771) == 0)
{
obj* x_772; obj* x_774; obj* x_776; obj* x_778; obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; 
x_772 = lean::cnstr_get(x_771, 0);
x_774 = lean::cnstr_get(x_771, 1);
x_776 = lean::cnstr_get(x_771, 2);
if (lean::is_exclusive(x_771)) {
 lean::cnstr_set(x_771, 0, lean::box(0));
 lean::cnstr_set(x_771, 1, lean::box(0));
 lean::cnstr_set(x_771, 2, lean::box(0));
 x_778 = x_771;
} else {
 lean::inc(x_772);
 lean::inc(x_774);
 lean::inc(x_776);
 lean::dec(x_771);
 x_778 = lean::box(0);
}
x_779 = lean::apply_1(x_316, x_772);
x_780 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_778)) {
 x_781 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_781 = x_778;
}
lean::cnstr_set(x_781, 0, x_779);
lean::cnstr_set(x_781, 1, x_774);
lean::cnstr_set(x_781, 2, x_780);
x_782 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_776, x_781);
x_783 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_782);
if (lean::obj_tag(x_783) == 0)
{
obj* x_784; obj* x_786; obj* x_788; 
x_784 = lean::cnstr_get(x_783, 0);
lean::inc(x_784);
x_786 = lean::cnstr_get(x_783, 1);
lean::inc(x_786);
x_788 = lean::cnstr_get(x_783, 2);
lean::inc(x_788);
lean::dec(x_783);
x_312 = x_784;
x_313 = x_786;
x_314 = x_788;
goto lbl_315;
}
else
{
obj* x_791; uint8 x_793; obj* x_794; obj* x_796; obj* x_797; 
x_791 = lean::cnstr_get(x_783, 0);
x_793 = lean::cnstr_get_scalar<uint8>(x_783, sizeof(void*)*1);
if (lean::is_exclusive(x_783)) {
 lean::cnstr_set(x_783, 0, lean::box(0));
 x_794 = x_783;
} else {
 lean::inc(x_791);
 lean::dec(x_783);
 x_794 = lean::box(0);
}
lean::inc(x_791);
if (lean::is_scalar(x_794)) {
 x_796 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_796 = x_794;
}
lean::cnstr_set(x_796, 0, x_791);
lean::cnstr_set_scalar(x_796, sizeof(void*)*1, x_793);
x_797 = x_796;
x_308 = x_797;
x_309 = x_791;
x_310 = x_793;
goto lbl_311;
}
}
else
{
obj* x_799; uint8 x_801; obj* x_802; obj* x_803; obj* x_804; obj* x_805; 
lean::dec(x_316);
x_799 = lean::cnstr_get(x_771, 0);
x_801 = lean::cnstr_get_scalar<uint8>(x_771, sizeof(void*)*1);
if (lean::is_exclusive(x_771)) {
 lean::cnstr_set(x_771, 0, lean::box(0));
 x_802 = x_771;
} else {
 lean::inc(x_799);
 lean::dec(x_771);
 x_802 = lean::box(0);
}
if (lean::is_scalar(x_802)) {
 x_803 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_803 = x_802;
}
lean::cnstr_set(x_803, 0, x_799);
lean::cnstr_set_scalar(x_803, sizeof(void*)*1, x_801);
x_804 = x_803;
x_805 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_804);
if (lean::obj_tag(x_805) == 0)
{
obj* x_806; obj* x_808; obj* x_810; 
x_806 = lean::cnstr_get(x_805, 0);
lean::inc(x_806);
x_808 = lean::cnstr_get(x_805, 1);
lean::inc(x_808);
x_810 = lean::cnstr_get(x_805, 2);
lean::inc(x_810);
lean::dec(x_805);
x_312 = x_806;
x_313 = x_808;
x_314 = x_810;
goto lbl_315;
}
else
{
obj* x_813; uint8 x_815; obj* x_816; obj* x_818; obj* x_819; 
x_813 = lean::cnstr_get(x_805, 0);
x_815 = lean::cnstr_get_scalar<uint8>(x_805, sizeof(void*)*1);
if (lean::is_exclusive(x_805)) {
 lean::cnstr_set(x_805, 0, lean::box(0));
 x_816 = x_805;
} else {
 lean::inc(x_813);
 lean::dec(x_805);
 x_816 = lean::box(0);
}
lean::inc(x_813);
if (lean::is_scalar(x_816)) {
 x_818 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_818 = x_816;
}
lean::cnstr_set(x_818, 0, x_813);
lean::cnstr_set_scalar(x_818, sizeof(void*)*1, x_815);
x_819 = x_818;
x_308 = x_819;
x_309 = x_813;
x_310 = x_815;
goto lbl_311;
}
}
}
}
lbl_234:
{
obj* x_820; 
x_820 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(x_232);
if (lean::obj_tag(x_820) == 0)
{
obj* x_821; obj* x_823; obj* x_825; obj* x_827; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; 
x_821 = lean::cnstr_get(x_820, 0);
x_823 = lean::cnstr_get(x_820, 1);
x_825 = lean::cnstr_get(x_820, 2);
if (lean::is_exclusive(x_820)) {
 lean::cnstr_set(x_820, 0, lean::box(0));
 lean::cnstr_set(x_820, 1, lean::box(0));
 lean::cnstr_set(x_820, 2, lean::box(0));
 x_827 = x_820;
} else {
 lean::inc(x_821);
 lean::inc(x_823);
 lean::inc(x_825);
 lean::dec(x_820);
 x_827 = lean::box(0);
}
x_828 = lean::apply_1(x_231, x_821);
x_829 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_827)) {
 x_830 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_830 = x_827;
}
lean::cnstr_set(x_830, 0, x_828);
lean::cnstr_set(x_830, 1, x_823);
lean::cnstr_set(x_830, 2, x_829);
x_831 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_825, x_830);
x_832 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_233, x_831);
if (lean::obj_tag(x_832) == 0)
{
obj* x_836; obj* x_837; obj* x_838; obj* x_839; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_836 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_832);
x_837 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_836);
x_838 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_837);
x_839 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_838);
return x_839;
}
else
{
obj* x_840; uint8 x_842; 
x_840 = lean::cnstr_get(x_832, 0);
lean::inc(x_840);
x_842 = lean::cnstr_get_scalar<uint8>(x_832, sizeof(void*)*1);
x_227 = x_832;
x_228 = x_840;
x_229 = x_842;
goto lbl_230;
}
}
else
{
obj* x_844; uint8 x_846; obj* x_847; obj* x_848; obj* x_849; obj* x_850; 
lean::dec(x_231);
x_844 = lean::cnstr_get(x_820, 0);
x_846 = lean::cnstr_get_scalar<uint8>(x_820, sizeof(void*)*1);
if (lean::is_exclusive(x_820)) {
 lean::cnstr_set(x_820, 0, lean::box(0));
 x_847 = x_820;
} else {
 lean::inc(x_844);
 lean::dec(x_820);
 x_847 = lean::box(0);
}
if (lean::is_scalar(x_847)) {
 x_848 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_848 = x_847;
}
lean::cnstr_set(x_848, 0, x_844);
lean::cnstr_set_scalar(x_848, sizeof(void*)*1, x_846);
x_849 = x_848;
x_850 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_233, x_849);
if (lean::obj_tag(x_850) == 0)
{
obj* x_854; obj* x_855; obj* x_856; obj* x_857; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_854 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_850);
x_855 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_854);
x_856 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_855);
x_857 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_856);
return x_857;
}
else
{
obj* x_858; uint8 x_860; 
x_858 = lean::cnstr_get(x_850, 0);
lean::inc(x_858);
x_860 = lean::cnstr_get_scalar<uint8>(x_850, sizeof(void*)*1);
x_227 = x_850;
x_228 = x_858;
x_229 = x_860;
goto lbl_230;
}
}
}
}
lbl_154:
{
obj* x_861; 
x_861 = l_lean_ir_parse__uint16(x_152);
if (lean::obj_tag(x_861) == 0)
{
obj* x_862; obj* x_864; obj* x_866; obj* x_868; obj* x_869; obj* x_870; obj* x_871; obj* x_872; obj* x_873; 
x_862 = lean::cnstr_get(x_861, 0);
x_864 = lean::cnstr_get(x_861, 1);
x_866 = lean::cnstr_get(x_861, 2);
if (lean::is_exclusive(x_861)) {
 lean::cnstr_set(x_861, 0, lean::box(0));
 lean::cnstr_set(x_861, 1, lean::box(0));
 lean::cnstr_set(x_861, 2, lean::box(0));
 x_868 = x_861;
} else {
 lean::inc(x_862);
 lean::inc(x_864);
 lean::inc(x_866);
 lean::dec(x_861);
 x_868 = lean::box(0);
}
x_869 = lean::apply_1(x_151, x_862);
x_870 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_868)) {
 x_871 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_871 = x_868;
}
lean::cnstr_set(x_871, 0, x_869);
lean::cnstr_set(x_871, 1, x_864);
lean::cnstr_set(x_871, 2, x_870);
x_872 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_866, x_871);
x_873 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_153, x_872);
if (lean::obj_tag(x_873) == 0)
{
obj* x_877; obj* x_878; obj* x_879; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_877 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_873);
x_878 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_877);
x_879 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_878);
return x_879;
}
else
{
obj* x_880; uint8 x_882; 
x_880 = lean::cnstr_get(x_873, 0);
lean::inc(x_880);
x_882 = lean::cnstr_get_scalar<uint8>(x_873, sizeof(void*)*1);
x_147 = x_873;
x_148 = x_880;
x_149 = x_882;
goto lbl_150;
}
}
else
{
obj* x_884; uint8 x_886; obj* x_887; obj* x_888; obj* x_889; obj* x_890; 
lean::dec(x_151);
x_884 = lean::cnstr_get(x_861, 0);
x_886 = lean::cnstr_get_scalar<uint8>(x_861, sizeof(void*)*1);
if (lean::is_exclusive(x_861)) {
 lean::cnstr_set(x_861, 0, lean::box(0));
 x_887 = x_861;
} else {
 lean::inc(x_884);
 lean::dec(x_861);
 x_887 = lean::box(0);
}
if (lean::is_scalar(x_887)) {
 x_888 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_888 = x_887;
}
lean::cnstr_set(x_888, 0, x_884);
lean::cnstr_set_scalar(x_888, sizeof(void*)*1, x_886);
x_889 = x_888;
x_890 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_153, x_889);
if (lean::obj_tag(x_890) == 0)
{
obj* x_894; obj* x_895; obj* x_896; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_894 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_890);
x_895 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_894);
x_896 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_895);
return x_896;
}
else
{
obj* x_897; uint8 x_899; 
x_897 = lean::cnstr_get(x_890, 0);
lean::inc(x_897);
x_899 = lean::cnstr_get_scalar<uint8>(x_890, sizeof(void*)*1);
x_147 = x_890;
x_148 = x_897;
x_149 = x_899;
goto lbl_150;
}
}
}
}
}
}
lbl_14:
{
obj* x_900; 
x_900 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(x_12);
if (lean::obj_tag(x_900) == 0)
{
obj* x_901; obj* x_903; obj* x_905; obj* x_907; obj* x_908; obj* x_909; obj* x_910; obj* x_911; obj* x_912; 
x_901 = lean::cnstr_get(x_900, 0);
x_903 = lean::cnstr_get(x_900, 1);
x_905 = lean::cnstr_get(x_900, 2);
if (lean::is_exclusive(x_900)) {
 lean::cnstr_set(x_900, 0, lean::box(0));
 lean::cnstr_set(x_900, 1, lean::box(0));
 lean::cnstr_set(x_900, 2, lean::box(0));
 x_907 = x_900;
} else {
 lean::inc(x_901);
 lean::inc(x_903);
 lean::inc(x_905);
 lean::dec(x_900);
 x_907 = lean::box(0);
}
x_908 = lean::apply_1(x_11, x_901);
x_909 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_907)) {
 x_910 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_910 = x_907;
}
lean::cnstr_set(x_910, 0, x_908);
lean::cnstr_set(x_910, 1, x_903);
lean::cnstr_set(x_910, 2, x_909);
x_911 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_905, x_910);
x_912 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_911);
x_9 = x_912;
goto lbl_10;
}
else
{
obj* x_914; uint8 x_916; obj* x_917; obj* x_918; obj* x_919; obj* x_920; 
lean::dec(x_11);
x_914 = lean::cnstr_get(x_900, 0);
x_916 = lean::cnstr_get_scalar<uint8>(x_900, sizeof(void*)*1);
if (lean::is_exclusive(x_900)) {
 lean::cnstr_set(x_900, 0, lean::box(0));
 x_917 = x_900;
} else {
 lean::inc(x_914);
 lean::dec(x_900);
 x_917 = lean::box(0);
}
if (lean::is_scalar(x_917)) {
 x_918 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_918 = x_917;
}
lean::cnstr_set(x_918, 0, x_914);
lean::cnstr_set_scalar(x_918, sizeof(void*)*1, x_916);
x_919 = x_918;
x_920 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_919);
x_9 = x_920;
goto lbl_10;
}
}
}
else
{
obj* x_922; uint8 x_924; obj* x_925; obj* x_926; obj* x_927; 
lean::dec(x_0);
x_922 = lean::cnstr_get(x_3, 0);
x_924 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_925 = x_3;
} else {
 lean::inc(x_922);
 lean::dec(x_3);
 x_925 = lean::box(0);
}
if (lean::is_scalar(x_925)) {
 x_926 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_926 = x_925;
}
lean::cnstr_set(x_926, 0, x_922);
lean::cnstr_set_scalar(x_926, sizeof(void*)*1, x_924);
x_927 = x_926;
return x_927;
}
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_parse__untyped__assignment___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint16 x_4; uint16 x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l_lean_ir_parse__untyped__assignment___lambda__3(x_0, x_4, x_5, x_6);
return x_7;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_lean_ir_parse__untyped__assignment___lambda__5(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_ir_parse__assignment(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__var(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_11; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_4);
lean::inc(x_2);
x_11 = l_lean_ir_parse__untyped__assignment(x_2, x_4);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
lean::dec(x_4);
lean::dec(x_2);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
return x_14;
}
else
{
obj* x_15; uint8 x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (x_17 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_11);
x_19 = l_lean_ir_parse__typed__assignment(x_2, x_4);
x_20 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_15, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_20);
return x_21;
}
else
{
obj* x_25; 
lean::dec(x_4);
lean::dec(x_15);
lean::dec(x_2);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
return x_25;
}
}
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_1, 0);
x_28 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_29 = x_1;
} else {
 lean::inc(x_26);
 lean::dec(x_1);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
return x_31;
}
}
}
obj* l_lean_ir_parse__instr___lambda__1(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(4, 1, 1);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set_scalar(x_2, sizeof(void*)*1, x_0);
x_3 = x_2;
return x_3;
}
}
obj* l_lean_ir_parse__instr___lambda__2(obj* x_0, usize x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(9, 2, sizeof(size_t)*1);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_1);
x_4 = x_3;
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__3(obj* x_0, uint16 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(7, 2, 2);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set_scalar(x_3, sizeof(void*)*2, x_1);
x_4 = x_3;
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(15, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* _init_l_lean_ir_parse__instr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("sset");
return x_0;
}
}
obj* _init_l_lean_ir_parse__instr___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("set");
return x_0;
}
}
obj* _init_l_lean_ir_parse__instr___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("array_write");
return x_0;
}
}
obj* l_lean_ir_parse__instr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_11 = l_lean_ir_parse__instr___closed__3;
lean::inc(x_0);
x_13 = l_lean_ir_keyword(x_11, x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_13, 1);
x_16 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_set(x_13, 1, lean::box(0));
 lean::cnstr_set(x_13, 2, lean::box(0));
 x_18 = x_13;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_parse__var(x_14);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__4), 3, 1);
lean::closure_set(x_27, 0, x_20);
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_22);
lean::cnstr_set(x_29, 2, x_28);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_34; obj* x_36; 
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 2);
lean::inc(x_36);
lean::dec(x_31);
x_7 = x_32;
x_8 = x_34;
x_9 = x_36;
goto lbl_10;
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_31, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_set(x_31, 0, lean::box(0));
 x_42 = x_31;
} else {
 lean::inc(x_39);
 lean::dec(x_31);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
x_1 = x_44;
goto lbl_2;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_18);
x_46 = lean::cnstr_get(x_19, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 x_49 = x_19;
} else {
 lean::inc(x_46);
 lean::dec(x_19);
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
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_7 = x_53;
x_8 = x_55;
x_9 = x_57;
goto lbl_10;
}
else
{
obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_60 = lean::cnstr_get(x_52, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 x_63 = x_52;
} else {
 lean::inc(x_60);
 lean::dec(x_52);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
x_1 = x_65;
goto lbl_2;
}
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_13, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_69 = x_13;
} else {
 lean::inc(x_66);
 lean::dec(x_13);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
x_1 = x_71;
goto lbl_2;
}
lbl_2:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; uint8 x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
x_73 = lean::cnstr_get(x_1, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_75 == 0)
{
obj* x_89; obj* x_91; 
lean::dec(x_1);
x_89 = l_lean_ir_parse__instr___closed__2;
lean::inc(x_0);
x_91 = l_lean_ir_keyword(x_89, x_0);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_97; 
x_92 = lean::cnstr_get(x_91, 1);
x_94 = lean::cnstr_get(x_91, 2);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_set(x_91, 1, lean::box(0));
 lean::cnstr_set(x_91, 2, lean::box(0));
 x_96 = x_91;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_91);
 x_96 = lean::box(0);
}
x_97 = l_lean_ir_parse__var(x_92);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_97, 2);
lean::inc(x_102);
lean::dec(x_97);
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__3___boxed), 3, 1);
lean::closure_set(x_105, 0, x_98);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_96)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_96;
}
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_100);
lean::cnstr_set(x_107, 2, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_114; 
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 2);
lean::inc(x_114);
lean::dec(x_109);
x_84 = x_110;
x_85 = x_112;
x_86 = x_114;
goto lbl_87;
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_122; obj* x_123; 
x_117 = lean::cnstr_get(x_109, 0);
x_119 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_set(x_109, 0, lean::box(0));
 x_120 = x_109;
} else {
 lean::inc(x_117);
 lean::dec(x_109);
 x_120 = lean::box(0);
}
lean::inc(x_117);
if (lean::is_scalar(x_120)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_120;
}
lean::cnstr_set(x_122, 0, x_117);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_119);
x_123 = x_122;
x_76 = x_123;
x_77 = x_117;
x_78 = x_119;
goto lbl_79;
}
}
else
{
obj* x_125; uint8 x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_96);
x_125 = lean::cnstr_get(x_97, 0);
x_127 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_set(x_97, 0, lean::box(0));
 x_128 = x_97;
} else {
 lean::inc(x_125);
 lean::dec(x_97);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_125);
lean::cnstr_set_scalar(x_129, sizeof(void*)*1, x_127);
x_130 = x_129;
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_130);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; obj* x_134; obj* x_136; 
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_131, 2);
lean::inc(x_136);
lean::dec(x_131);
x_84 = x_132;
x_85 = x_134;
x_86 = x_136;
goto lbl_87;
}
else
{
obj* x_139; uint8 x_141; obj* x_142; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_131, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_131, sizeof(void*)*1);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_set(x_131, 0, lean::box(0));
 x_142 = x_131;
} else {
 lean::inc(x_139);
 lean::dec(x_131);
 x_142 = lean::box(0);
}
lean::inc(x_139);
if (lean::is_scalar(x_142)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_142;
}
lean::cnstr_set(x_144, 0, x_139);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_141);
x_145 = x_144;
x_76 = x_145;
x_77 = x_139;
x_78 = x_141;
goto lbl_79;
}
}
}
else
{
obj* x_146; uint8 x_148; obj* x_149; obj* x_151; obj* x_152; 
x_146 = lean::cnstr_get(x_91, 0);
x_148 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_set(x_91, 0, lean::box(0));
 x_149 = x_91;
} else {
 lean::inc(x_146);
 lean::dec(x_91);
 x_149 = lean::box(0);
}
lean::inc(x_146);
if (lean::is_scalar(x_149)) {
 x_151 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_151 = x_149;
}
lean::cnstr_set(x_151, 0, x_146);
lean::cnstr_set_scalar(x_151, sizeof(void*)*1, x_148);
x_152 = x_151;
x_76 = x_152;
x_77 = x_146;
x_78 = x_148;
goto lbl_79;
}
}
else
{
lean::dec(x_0);
lean::dec(x_73);
return x_1;
}
lbl_79:
{
obj* x_155; obj* x_156; uint8 x_157; obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; 
if (x_78 == 0)
{
obj* x_168; obj* x_170; 
lean::dec(x_76);
x_168 = l_lean_ir_parse__instr___closed__1;
lean::inc(x_0);
x_170 = l_lean_ir_keyword(x_168, x_0);
if (lean::obj_tag(x_170) == 0)
{
obj* x_171; obj* x_173; obj* x_175; obj* x_176; 
x_171 = lean::cnstr_get(x_170, 1);
x_173 = lean::cnstr_get(x_170, 2);
if (lean::is_exclusive(x_170)) {
 lean::cnstr_release(x_170, 0);
 lean::cnstr_set(x_170, 1, lean::box(0));
 lean::cnstr_set(x_170, 2, lean::box(0));
 x_175 = x_170;
} else {
 lean::inc(x_171);
 lean::inc(x_173);
 lean::dec(x_170);
 x_175 = lean::box(0);
}
x_176 = l_lean_ir_parse__var(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 2);
lean::inc(x_181);
lean::dec(x_176);
x_184 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__2___boxed), 3, 1);
lean::closure_set(x_184, 0, x_177);
x_185 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_175)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_175;
}
lean::cnstr_set(x_186, 0, x_184);
lean::cnstr_set(x_186, 1, x_179);
lean::cnstr_set(x_186, 2, x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_186);
x_188 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_189; obj* x_191; obj* x_193; 
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_188, 1);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_188, 2);
lean::inc(x_193);
lean::dec(x_188);
x_163 = x_189;
x_164 = x_191;
x_165 = x_193;
goto lbl_166;
}
else
{
obj* x_196; uint8 x_198; obj* x_199; obj* x_201; obj* x_202; 
x_196 = lean::cnstr_get(x_188, 0);
x_198 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*1);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_set(x_188, 0, lean::box(0));
 x_199 = x_188;
} else {
 lean::inc(x_196);
 lean::dec(x_188);
 x_199 = lean::box(0);
}
lean::inc(x_196);
if (lean::is_scalar(x_199)) {
 x_201 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_201 = x_199;
}
lean::cnstr_set(x_201, 0, x_196);
lean::cnstr_set_scalar(x_201, sizeof(void*)*1, x_198);
x_202 = x_201;
x_155 = x_202;
x_156 = x_196;
x_157 = x_198;
goto lbl_158;
}
}
else
{
obj* x_204; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_175);
x_204 = lean::cnstr_get(x_176, 0);
x_206 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
 lean::cnstr_set(x_176, 0, lean::box(0));
 x_207 = x_176;
} else {
 lean::inc(x_204);
 lean::dec(x_176);
 x_207 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_204);
lean::cnstr_set_scalar(x_208, sizeof(void*)*1, x_206);
x_209 = x_208;
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_211; obj* x_213; obj* x_215; 
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_210, 1);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_210, 2);
lean::inc(x_215);
lean::dec(x_210);
x_163 = x_211;
x_164 = x_213;
x_165 = x_215;
goto lbl_166;
}
else
{
obj* x_218; uint8 x_220; obj* x_221; obj* x_223; obj* x_224; 
x_218 = lean::cnstr_get(x_210, 0);
x_220 = lean::cnstr_get_scalar<uint8>(x_210, sizeof(void*)*1);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_set(x_210, 0, lean::box(0));
 x_221 = x_210;
} else {
 lean::inc(x_218);
 lean::dec(x_210);
 x_221 = lean::box(0);
}
lean::inc(x_218);
if (lean::is_scalar(x_221)) {
 x_223 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_223 = x_221;
}
lean::cnstr_set(x_223, 0, x_218);
lean::cnstr_set_scalar(x_223, sizeof(void*)*1, x_220);
x_224 = x_223;
x_155 = x_224;
x_156 = x_218;
x_157 = x_220;
goto lbl_158;
}
}
}
else
{
obj* x_225; uint8 x_227; obj* x_228; obj* x_230; obj* x_231; 
x_225 = lean::cnstr_get(x_170, 0);
x_227 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_exclusive(x_170)) {
 lean::cnstr_set(x_170, 0, lean::box(0));
 x_228 = x_170;
} else {
 lean::inc(x_225);
 lean::dec(x_170);
 x_228 = lean::box(0);
}
lean::inc(x_225);
if (lean::is_scalar(x_228)) {
 x_230 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_230 = x_228;
}
lean::cnstr_set(x_230, 0, x_225);
lean::cnstr_set_scalar(x_230, sizeof(void*)*1, x_227);
x_231 = x_230;
x_155 = x_231;
x_156 = x_225;
x_157 = x_227;
goto lbl_158;
}
}
else
{
obj* x_234; 
lean::dec(x_77);
lean::dec(x_0);
x_234 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_76);
return x_234;
}
lbl_158:
{
obj* x_235; obj* x_236; obj* x_237; 
if (x_157 == 0)
{
obj* x_240; obj* x_241; obj* x_243; 
lean::dec(x_155);
x_240 = l_lean_ir_parse__typed__assignment___closed__5;
x_241 = l_lean_ir_str2unop;
lean::inc(x_0);
x_243 = l_lean_ir_parse__key2val___main___rarg(x_240, x_241, x_0);
if (lean::obj_tag(x_243) == 0)
{
obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_244 = lean::cnstr_get(x_243, 0);
x_246 = lean::cnstr_get(x_243, 1);
x_248 = lean::cnstr_get(x_243, 2);
if (lean::is_exclusive(x_243)) {
 lean::cnstr_set(x_243, 0, lean::box(0));
 lean::cnstr_set(x_243, 1, lean::box(0));
 lean::cnstr_set(x_243, 2, lean::box(0));
 x_250 = x_243;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::dec(x_243);
 x_250 = lean::box(0);
}
x_251 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__1___boxed), 2, 1);
lean::closure_set(x_251, 0, x_244);
x_252 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_250)) {
 x_253 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_253 = x_250;
}
lean::cnstr_set(x_253, 0, x_251);
lean::cnstr_set(x_253, 1, x_246);
lean::cnstr_set(x_253, 2, x_252);
x_254 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_248, x_253);
if (lean::obj_tag(x_254) == 0)
{
obj* x_255; obj* x_257; obj* x_259; 
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
x_257 = lean::cnstr_get(x_254, 1);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_254, 2);
lean::inc(x_259);
lean::dec(x_254);
x_235 = x_255;
x_236 = x_257;
x_237 = x_259;
goto lbl_238;
}
else
{
obj* x_262; uint8 x_264; obj* x_265; 
x_262 = lean::cnstr_get(x_254, 0);
x_264 = lean::cnstr_get_scalar<uint8>(x_254, sizeof(void*)*1);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_set(x_254, 0, lean::box(0));
 x_265 = x_254;
} else {
 lean::inc(x_262);
 lean::dec(x_254);
 x_265 = lean::box(0);
}
if (x_264 == 0)
{
obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
lean::dec(x_265);
x_267 = l_lean_ir_parse__assignment(x_0);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_262, x_267);
x_269 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_268);
x_270 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_269);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_270);
return x_271;
}
else
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_0);
if (lean::is_scalar(x_265)) {
 x_273 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_273 = x_265;
}
lean::cnstr_set(x_273, 0, x_262);
lean::cnstr_set_scalar(x_273, sizeof(void*)*1, x_264);
x_274 = x_273;
x_275 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_274);
x_276 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_275);
x_277 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_276);
return x_277;
}
}
}
else
{
obj* x_278; uint8 x_280; obj* x_281; 
x_278 = lean::cnstr_get(x_243, 0);
x_280 = lean::cnstr_get_scalar<uint8>(x_243, sizeof(void*)*1);
if (lean::is_exclusive(x_243)) {
 lean::cnstr_set(x_243, 0, lean::box(0));
 x_281 = x_243;
} else {
 lean::inc(x_278);
 lean::dec(x_243);
 x_281 = lean::box(0);
}
if (x_280 == 0)
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_281);
x_283 = l_lean_ir_parse__assignment(x_0);
x_284 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_278, x_283);
x_285 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_284);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_285);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_286);
return x_287;
}
else
{
obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
lean::dec(x_0);
if (lean::is_scalar(x_281)) {
 x_289 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_289 = x_281;
}
lean::cnstr_set(x_289, 0, x_278);
lean::cnstr_set_scalar(x_289, sizeof(void*)*1, x_280);
x_290 = x_289;
x_291 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_290);
x_292 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_291);
x_293 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_292);
return x_293;
}
}
}
else
{
obj* x_296; obj* x_297; 
lean::dec(x_156);
lean::dec(x_0);
x_296 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_155);
x_297 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_296);
return x_297;
}
lbl_238:
{
obj* x_298; 
x_298 = l_lean_ir_parse__var(x_236);
if (lean::obj_tag(x_298) == 0)
{
obj* x_299; obj* x_301; obj* x_303; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; 
x_299 = lean::cnstr_get(x_298, 0);
x_301 = lean::cnstr_get(x_298, 1);
x_303 = lean::cnstr_get(x_298, 2);
if (lean::is_exclusive(x_298)) {
 lean::cnstr_set(x_298, 0, lean::box(0));
 lean::cnstr_set(x_298, 1, lean::box(0));
 lean::cnstr_set(x_298, 2, lean::box(0));
 x_305 = x_298;
} else {
 lean::inc(x_299);
 lean::inc(x_301);
 lean::inc(x_303);
 lean::dec(x_298);
 x_305 = lean::box(0);
}
x_306 = lean::apply_1(x_235, x_299);
x_307 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_305)) {
 x_308 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_308 = x_305;
}
lean::cnstr_set(x_308, 0, x_306);
lean::cnstr_set(x_308, 1, x_301);
lean::cnstr_set(x_308, 2, x_307);
x_309 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_303, x_308);
x_310 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_237, x_309);
if (lean::obj_tag(x_310) == 0)
{
obj* x_312; obj* x_313; obj* x_314; 
lean::dec(x_0);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_310);
x_313 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_312);
x_314 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_313);
return x_314;
}
else
{
obj* x_315; uint8 x_317; 
x_315 = lean::cnstr_get(x_310, 0);
lean::inc(x_315);
x_317 = lean::cnstr_get_scalar<uint8>(x_310, sizeof(void*)*1);
if (x_317 == 0)
{
obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_310);
x_319 = l_lean_ir_parse__assignment(x_0);
x_320 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_315, x_319);
x_321 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_320);
x_322 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_321);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_322);
return x_323;
}
else
{
obj* x_326; obj* x_327; obj* x_328; 
lean::dec(x_0);
lean::dec(x_315);
x_326 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_310);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_326);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_327);
return x_328;
}
}
}
else
{
obj* x_330; uint8 x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_235);
x_330 = lean::cnstr_get(x_298, 0);
x_332 = lean::cnstr_get_scalar<uint8>(x_298, sizeof(void*)*1);
if (lean::is_exclusive(x_298)) {
 lean::cnstr_set(x_298, 0, lean::box(0));
 x_333 = x_298;
} else {
 lean::inc(x_330);
 lean::dec(x_298);
 x_333 = lean::box(0);
}
if (lean::is_scalar(x_333)) {
 x_334 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_334 = x_333;
}
lean::cnstr_set(x_334, 0, x_330);
lean::cnstr_set_scalar(x_334, sizeof(void*)*1, x_332);
x_335 = x_334;
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_237, x_335);
if (lean::obj_tag(x_336) == 0)
{
obj* x_338; obj* x_339; obj* x_340; 
lean::dec(x_0);
x_338 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_336);
x_339 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_338);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_339);
return x_340;
}
else
{
obj* x_341; uint8 x_343; 
x_341 = lean::cnstr_get(x_336, 0);
lean::inc(x_341);
x_343 = lean::cnstr_get_scalar<uint8>(x_336, sizeof(void*)*1);
if (x_343 == 0)
{
obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_336);
x_345 = l_lean_ir_parse__assignment(x_0);
x_346 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_341, x_345);
x_347 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_346);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_347);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_348);
return x_349;
}
else
{
obj* x_352; obj* x_353; obj* x_354; 
lean::dec(x_0);
lean::dec(x_341);
x_352 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_336);
x_353 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_352);
x_354 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_353);
return x_354;
}
}
}
}
}
lbl_162:
{
obj* x_355; 
x_355 = l_lean_ir_parse__var(x_160);
if (lean::obj_tag(x_355) == 0)
{
obj* x_356; obj* x_358; obj* x_360; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
x_356 = lean::cnstr_get(x_355, 0);
x_358 = lean::cnstr_get(x_355, 1);
x_360 = lean::cnstr_get(x_355, 2);
if (lean::is_exclusive(x_355)) {
 lean::cnstr_set(x_355, 0, lean::box(0));
 lean::cnstr_set(x_355, 1, lean::box(0));
 lean::cnstr_set(x_355, 2, lean::box(0));
 x_362 = x_355;
} else {
 lean::inc(x_356);
 lean::inc(x_358);
 lean::inc(x_360);
 lean::dec(x_355);
 x_362 = lean::box(0);
}
x_363 = lean::apply_1(x_159, x_356);
x_364 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_362)) {
 x_365 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_365 = x_362;
}
lean::cnstr_set(x_365, 0, x_363);
lean::cnstr_set(x_365, 1, x_358);
lean::cnstr_set(x_365, 2, x_364);
x_366 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_360, x_365);
x_367 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_366);
if (lean::obj_tag(x_367) == 0)
{
obj* x_369; obj* x_370; 
lean::dec(x_0);
x_369 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_367);
x_370 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_369);
return x_370;
}
else
{
obj* x_371; uint8 x_373; 
x_371 = lean::cnstr_get(x_367, 0);
lean::inc(x_371);
x_373 = lean::cnstr_get_scalar<uint8>(x_367, sizeof(void*)*1);
x_155 = x_367;
x_156 = x_371;
x_157 = x_373;
goto lbl_158;
}
}
else
{
obj* x_375; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_159);
x_375 = lean::cnstr_get(x_355, 0);
x_377 = lean::cnstr_get_scalar<uint8>(x_355, sizeof(void*)*1);
if (lean::is_exclusive(x_355)) {
 lean::cnstr_set(x_355, 0, lean::box(0));
 x_378 = x_355;
} else {
 lean::inc(x_375);
 lean::dec(x_355);
 x_378 = lean::box(0);
}
if (lean::is_scalar(x_378)) {
 x_379 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_379 = x_378;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set_scalar(x_379, sizeof(void*)*1, x_377);
x_380 = x_379;
x_381 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_380);
if (lean::obj_tag(x_381) == 0)
{
obj* x_383; obj* x_384; 
lean::dec(x_0);
x_383 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_381);
x_384 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_383);
return x_384;
}
else
{
obj* x_385; uint8 x_387; 
x_385 = lean::cnstr_get(x_381, 0);
lean::inc(x_385);
x_387 = lean::cnstr_get_scalar<uint8>(x_381, sizeof(void*)*1);
x_155 = x_381;
x_156 = x_385;
x_157 = x_387;
goto lbl_158;
}
}
}
lbl_166:
{
obj* x_388; 
x_388 = l_lean_ir_parse__usize(x_164);
if (lean::obj_tag(x_388) == 0)
{
obj* x_389; obj* x_391; obj* x_393; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_389 = lean::cnstr_get(x_388, 0);
x_391 = lean::cnstr_get(x_388, 1);
x_393 = lean::cnstr_get(x_388, 2);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_set(x_388, 0, lean::box(0));
 lean::cnstr_set(x_388, 1, lean::box(0));
 lean::cnstr_set(x_388, 2, lean::box(0));
 x_395 = x_388;
} else {
 lean::inc(x_389);
 lean::inc(x_391);
 lean::inc(x_393);
 lean::dec(x_388);
 x_395 = lean::box(0);
}
x_396 = lean::apply_1(x_163, x_389);
x_397 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_395)) {
 x_398 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_398 = x_395;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_391);
lean::cnstr_set(x_398, 2, x_397);
x_399 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_393, x_398);
x_400 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_399);
if (lean::obj_tag(x_400) == 0)
{
obj* x_401; obj* x_403; obj* x_405; 
x_401 = lean::cnstr_get(x_400, 0);
lean::inc(x_401);
x_403 = lean::cnstr_get(x_400, 1);
lean::inc(x_403);
x_405 = lean::cnstr_get(x_400, 2);
lean::inc(x_405);
lean::dec(x_400);
x_159 = x_401;
x_160 = x_403;
x_161 = x_405;
goto lbl_162;
}
else
{
obj* x_408; uint8 x_410; obj* x_411; obj* x_413; obj* x_414; 
x_408 = lean::cnstr_get(x_400, 0);
x_410 = lean::cnstr_get_scalar<uint8>(x_400, sizeof(void*)*1);
if (lean::is_exclusive(x_400)) {
 lean::cnstr_set(x_400, 0, lean::box(0));
 x_411 = x_400;
} else {
 lean::inc(x_408);
 lean::dec(x_400);
 x_411 = lean::box(0);
}
lean::inc(x_408);
if (lean::is_scalar(x_411)) {
 x_413 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_413 = x_411;
}
lean::cnstr_set(x_413, 0, x_408);
lean::cnstr_set_scalar(x_413, sizeof(void*)*1, x_410);
x_414 = x_413;
x_155 = x_414;
x_156 = x_408;
x_157 = x_410;
goto lbl_158;
}
}
else
{
obj* x_416; uint8 x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
lean::dec(x_163);
x_416 = lean::cnstr_get(x_388, 0);
x_418 = lean::cnstr_get_scalar<uint8>(x_388, sizeof(void*)*1);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_set(x_388, 0, lean::box(0));
 x_419 = x_388;
} else {
 lean::inc(x_416);
 lean::dec(x_388);
 x_419 = lean::box(0);
}
if (lean::is_scalar(x_419)) {
 x_420 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_420 = x_419;
}
lean::cnstr_set(x_420, 0, x_416);
lean::cnstr_set_scalar(x_420, sizeof(void*)*1, x_418);
x_421 = x_420;
x_422 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_421);
if (lean::obj_tag(x_422) == 0)
{
obj* x_423; obj* x_425; obj* x_427; 
x_423 = lean::cnstr_get(x_422, 0);
lean::inc(x_423);
x_425 = lean::cnstr_get(x_422, 1);
lean::inc(x_425);
x_427 = lean::cnstr_get(x_422, 2);
lean::inc(x_427);
lean::dec(x_422);
x_159 = x_423;
x_160 = x_425;
x_161 = x_427;
goto lbl_162;
}
else
{
obj* x_430; uint8 x_432; obj* x_433; obj* x_435; obj* x_436; 
x_430 = lean::cnstr_get(x_422, 0);
x_432 = lean::cnstr_get_scalar<uint8>(x_422, sizeof(void*)*1);
if (lean::is_exclusive(x_422)) {
 lean::cnstr_set(x_422, 0, lean::box(0));
 x_433 = x_422;
} else {
 lean::inc(x_430);
 lean::dec(x_422);
 x_433 = lean::box(0);
}
lean::inc(x_430);
if (lean::is_scalar(x_433)) {
 x_435 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_435 = x_433;
}
lean::cnstr_set(x_435, 0, x_430);
lean::cnstr_set_scalar(x_435, sizeof(void*)*1, x_432);
x_436 = x_435;
x_155 = x_436;
x_156 = x_430;
x_157 = x_432;
goto lbl_158;
}
}
}
}
lbl_83:
{
obj* x_437; 
x_437 = l_lean_ir_parse__var(x_81);
if (lean::obj_tag(x_437) == 0)
{
obj* x_438; obj* x_440; obj* x_442; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; obj* x_449; 
x_438 = lean::cnstr_get(x_437, 0);
x_440 = lean::cnstr_get(x_437, 1);
x_442 = lean::cnstr_get(x_437, 2);
if (lean::is_exclusive(x_437)) {
 lean::cnstr_set(x_437, 0, lean::box(0));
 lean::cnstr_set(x_437, 1, lean::box(0));
 lean::cnstr_set(x_437, 2, lean::box(0));
 x_444 = x_437;
} else {
 lean::inc(x_438);
 lean::inc(x_440);
 lean::inc(x_442);
 lean::dec(x_437);
 x_444 = lean::box(0);
}
x_445 = lean::apply_1(x_80, x_438);
x_446 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_444)) {
 x_447 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_447 = x_444;
}
lean::cnstr_set(x_447, 0, x_445);
lean::cnstr_set(x_447, 1, x_440);
lean::cnstr_set(x_447, 2, x_446);
x_448 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_442, x_447);
x_449 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_448);
if (lean::obj_tag(x_449) == 0)
{
obj* x_451; 
lean::dec(x_0);
x_451 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_449);
return x_451;
}
else
{
obj* x_452; uint8 x_454; 
x_452 = lean::cnstr_get(x_449, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get_scalar<uint8>(x_449, sizeof(void*)*1);
x_76 = x_449;
x_77 = x_452;
x_78 = x_454;
goto lbl_79;
}
}
else
{
obj* x_456; uint8 x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; 
lean::dec(x_80);
x_456 = lean::cnstr_get(x_437, 0);
x_458 = lean::cnstr_get_scalar<uint8>(x_437, sizeof(void*)*1);
if (lean::is_exclusive(x_437)) {
 lean::cnstr_set(x_437, 0, lean::box(0));
 x_459 = x_437;
} else {
 lean::inc(x_456);
 lean::dec(x_437);
 x_459 = lean::box(0);
}
if (lean::is_scalar(x_459)) {
 x_460 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_460 = x_459;
}
lean::cnstr_set(x_460, 0, x_456);
lean::cnstr_set_scalar(x_460, sizeof(void*)*1, x_458);
x_461 = x_460;
x_462 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_461);
if (lean::obj_tag(x_462) == 0)
{
obj* x_464; 
lean::dec(x_0);
x_464 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_462);
return x_464;
}
else
{
obj* x_465; uint8 x_467; 
x_465 = lean::cnstr_get(x_462, 0);
lean::inc(x_465);
x_467 = lean::cnstr_get_scalar<uint8>(x_462, sizeof(void*)*1);
x_76 = x_462;
x_77 = x_465;
x_78 = x_467;
goto lbl_79;
}
}
}
lbl_87:
{
obj* x_468; 
x_468 = l_lean_ir_parse__uint16(x_85);
if (lean::obj_tag(x_468) == 0)
{
obj* x_469; obj* x_471; obj* x_473; obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; 
x_469 = lean::cnstr_get(x_468, 0);
x_471 = lean::cnstr_get(x_468, 1);
x_473 = lean::cnstr_get(x_468, 2);
if (lean::is_exclusive(x_468)) {
 lean::cnstr_set(x_468, 0, lean::box(0));
 lean::cnstr_set(x_468, 1, lean::box(0));
 lean::cnstr_set(x_468, 2, lean::box(0));
 x_475 = x_468;
} else {
 lean::inc(x_469);
 lean::inc(x_471);
 lean::inc(x_473);
 lean::dec(x_468);
 x_475 = lean::box(0);
}
x_476 = lean::apply_1(x_84, x_469);
x_477 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_475)) {
 x_478 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_478 = x_475;
}
lean::cnstr_set(x_478, 0, x_476);
lean::cnstr_set(x_478, 1, x_471);
lean::cnstr_set(x_478, 2, x_477);
x_479 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_473, x_478);
x_480 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_479);
if (lean::obj_tag(x_480) == 0)
{
obj* x_481; obj* x_483; obj* x_485; 
x_481 = lean::cnstr_get(x_480, 0);
lean::inc(x_481);
x_483 = lean::cnstr_get(x_480, 1);
lean::inc(x_483);
x_485 = lean::cnstr_get(x_480, 2);
lean::inc(x_485);
lean::dec(x_480);
x_80 = x_481;
x_81 = x_483;
x_82 = x_485;
goto lbl_83;
}
else
{
obj* x_488; uint8 x_490; obj* x_491; obj* x_493; obj* x_494; 
x_488 = lean::cnstr_get(x_480, 0);
x_490 = lean::cnstr_get_scalar<uint8>(x_480, sizeof(void*)*1);
if (lean::is_exclusive(x_480)) {
 lean::cnstr_set(x_480, 0, lean::box(0));
 x_491 = x_480;
} else {
 lean::inc(x_488);
 lean::dec(x_480);
 x_491 = lean::box(0);
}
lean::inc(x_488);
if (lean::is_scalar(x_491)) {
 x_493 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_493 = x_491;
}
lean::cnstr_set(x_493, 0, x_488);
lean::cnstr_set_scalar(x_493, sizeof(void*)*1, x_490);
x_494 = x_493;
x_76 = x_494;
x_77 = x_488;
x_78 = x_490;
goto lbl_79;
}
}
else
{
obj* x_496; uint8 x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; 
lean::dec(x_84);
x_496 = lean::cnstr_get(x_468, 0);
x_498 = lean::cnstr_get_scalar<uint8>(x_468, sizeof(void*)*1);
if (lean::is_exclusive(x_468)) {
 lean::cnstr_set(x_468, 0, lean::box(0));
 x_499 = x_468;
} else {
 lean::inc(x_496);
 lean::dec(x_468);
 x_499 = lean::box(0);
}
if (lean::is_scalar(x_499)) {
 x_500 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_500 = x_499;
}
lean::cnstr_set(x_500, 0, x_496);
lean::cnstr_set_scalar(x_500, sizeof(void*)*1, x_498);
x_501 = x_500;
x_502 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_501);
if (lean::obj_tag(x_502) == 0)
{
obj* x_503; obj* x_505; obj* x_507; 
x_503 = lean::cnstr_get(x_502, 0);
lean::inc(x_503);
x_505 = lean::cnstr_get(x_502, 1);
lean::inc(x_505);
x_507 = lean::cnstr_get(x_502, 2);
lean::inc(x_507);
lean::dec(x_502);
x_80 = x_503;
x_81 = x_505;
x_82 = x_507;
goto lbl_83;
}
else
{
obj* x_510; uint8 x_512; obj* x_513; obj* x_515; obj* x_516; 
x_510 = lean::cnstr_get(x_502, 0);
x_512 = lean::cnstr_get_scalar<uint8>(x_502, sizeof(void*)*1);
if (lean::is_exclusive(x_502)) {
 lean::cnstr_set(x_502, 0, lean::box(0));
 x_513 = x_502;
} else {
 lean::inc(x_510);
 lean::dec(x_502);
 x_513 = lean::box(0);
}
lean::inc(x_510);
if (lean::is_scalar(x_513)) {
 x_515 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_515 = x_513;
}
lean::cnstr_set(x_515, 0, x_510);
lean::cnstr_set_scalar(x_515, sizeof(void*)*1, x_512);
x_516 = x_515;
x_76 = x_516;
x_77 = x_510;
x_78 = x_512;
goto lbl_79;
}
}
}
}
}
lbl_6:
{
obj* x_517; 
x_517 = l_lean_ir_parse__var(x_4);
if (lean::obj_tag(x_517) == 0)
{
obj* x_518; obj* x_520; obj* x_522; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; 
x_518 = lean::cnstr_get(x_517, 0);
x_520 = lean::cnstr_get(x_517, 1);
x_522 = lean::cnstr_get(x_517, 2);
if (lean::is_exclusive(x_517)) {
 lean::cnstr_set(x_517, 0, lean::box(0));
 lean::cnstr_set(x_517, 1, lean::box(0));
 lean::cnstr_set(x_517, 2, lean::box(0));
 x_524 = x_517;
} else {
 lean::inc(x_518);
 lean::inc(x_520);
 lean::inc(x_522);
 lean::dec(x_517);
 x_524 = lean::box(0);
}
x_525 = lean::apply_1(x_3, x_518);
x_526 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_524)) {
 x_527 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_527 = x_524;
}
lean::cnstr_set(x_527, 0, x_525);
lean::cnstr_set(x_527, 1, x_520);
lean::cnstr_set(x_527, 2, x_526);
x_528 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_522, x_527);
x_529 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_528);
x_1 = x_529;
goto lbl_2;
}
else
{
obj* x_531; uint8 x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; 
lean::dec(x_3);
x_531 = lean::cnstr_get(x_517, 0);
x_533 = lean::cnstr_get_scalar<uint8>(x_517, sizeof(void*)*1);
if (lean::is_exclusive(x_517)) {
 lean::cnstr_set(x_517, 0, lean::box(0));
 x_534 = x_517;
} else {
 lean::inc(x_531);
 lean::dec(x_517);
 x_534 = lean::box(0);
}
if (lean::is_scalar(x_534)) {
 x_535 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_535 = x_534;
}
lean::cnstr_set(x_535, 0, x_531);
lean::cnstr_set_scalar(x_535, sizeof(void*)*1, x_533);
x_536 = x_535;
x_537 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_536);
x_1 = x_537;
goto lbl_2;
}
}
lbl_10:
{
obj* x_538; 
x_538 = l_lean_ir_parse__var(x_8);
if (lean::obj_tag(x_538) == 0)
{
obj* x_539; obj* x_541; obj* x_543; obj* x_545; obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; 
x_539 = lean::cnstr_get(x_538, 0);
x_541 = lean::cnstr_get(x_538, 1);
x_543 = lean::cnstr_get(x_538, 2);
if (lean::is_exclusive(x_538)) {
 lean::cnstr_set(x_538, 0, lean::box(0));
 lean::cnstr_set(x_538, 1, lean::box(0));
 lean::cnstr_set(x_538, 2, lean::box(0));
 x_545 = x_538;
} else {
 lean::inc(x_539);
 lean::inc(x_541);
 lean::inc(x_543);
 lean::dec(x_538);
 x_545 = lean::box(0);
}
x_546 = lean::apply_1(x_7, x_539);
x_547 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_545)) {
 x_548 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_548 = x_545;
}
lean::cnstr_set(x_548, 0, x_546);
lean::cnstr_set(x_548, 1, x_541);
lean::cnstr_set(x_548, 2, x_547);
x_549 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_543, x_548);
x_550 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_549);
if (lean::obj_tag(x_550) == 0)
{
obj* x_551; obj* x_553; obj* x_555; 
x_551 = lean::cnstr_get(x_550, 0);
lean::inc(x_551);
x_553 = lean::cnstr_get(x_550, 1);
lean::inc(x_553);
x_555 = lean::cnstr_get(x_550, 2);
lean::inc(x_555);
lean::dec(x_550);
x_3 = x_551;
x_4 = x_553;
x_5 = x_555;
goto lbl_6;
}
else
{
obj* x_558; uint8 x_560; obj* x_561; obj* x_562; obj* x_563; 
x_558 = lean::cnstr_get(x_550, 0);
x_560 = lean::cnstr_get_scalar<uint8>(x_550, sizeof(void*)*1);
if (lean::is_exclusive(x_550)) {
 lean::cnstr_set(x_550, 0, lean::box(0));
 x_561 = x_550;
} else {
 lean::inc(x_558);
 lean::dec(x_550);
 x_561 = lean::box(0);
}
if (lean::is_scalar(x_561)) {
 x_562 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_562 = x_561;
}
lean::cnstr_set(x_562, 0, x_558);
lean::cnstr_set_scalar(x_562, sizeof(void*)*1, x_560);
x_563 = x_562;
x_1 = x_563;
goto lbl_2;
}
}
else
{
obj* x_565; uint8 x_567; obj* x_568; obj* x_569; obj* x_570; obj* x_571; 
lean::dec(x_7);
x_565 = lean::cnstr_get(x_538, 0);
x_567 = lean::cnstr_get_scalar<uint8>(x_538, sizeof(void*)*1);
if (lean::is_exclusive(x_538)) {
 lean::cnstr_set(x_538, 0, lean::box(0));
 x_568 = x_538;
} else {
 lean::inc(x_565);
 lean::dec(x_538);
 x_568 = lean::box(0);
}
if (lean::is_scalar(x_568)) {
 x_569 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_569 = x_568;
}
lean::cnstr_set(x_569, 0, x_565);
lean::cnstr_set_scalar(x_569, sizeof(void*)*1, x_567);
x_570 = x_569;
x_571 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_570);
if (lean::obj_tag(x_571) == 0)
{
obj* x_572; obj* x_574; obj* x_576; 
x_572 = lean::cnstr_get(x_571, 0);
lean::inc(x_572);
x_574 = lean::cnstr_get(x_571, 1);
lean::inc(x_574);
x_576 = lean::cnstr_get(x_571, 2);
lean::inc(x_576);
lean::dec(x_571);
x_3 = x_572;
x_4 = x_574;
x_5 = x_576;
goto lbl_6;
}
else
{
obj* x_579; uint8 x_581; obj* x_582; obj* x_583; obj* x_584; 
x_579 = lean::cnstr_get(x_571, 0);
x_581 = lean::cnstr_get_scalar<uint8>(x_571, sizeof(void*)*1);
if (lean::is_exclusive(x_571)) {
 lean::cnstr_set(x_571, 0, lean::box(0));
 x_582 = x_571;
} else {
 lean::inc(x_579);
 lean::dec(x_571);
 x_582 = lean::box(0);
}
if (lean::is_scalar(x_582)) {
 x_583 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_583 = x_582;
}
lean::cnstr_set(x_583, 0, x_579);
lean::cnstr_set_scalar(x_583, sizeof(void*)*1, x_581);
x_584 = x_583;
x_1 = x_584;
goto lbl_2;
}
}
}
}
}
obj* l_lean_ir_parse__instr___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_lean_ir_parse__instr___lambda__1(x_2, x_1);
return x_3;
}
}
obj* l_lean_ir_parse__instr___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = l_lean_ir_parse__instr___lambda__2(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_parse__instr___lambda__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* _init_l_lean_ir_parse__phi___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("phi");
return x_0;
}
}
obj* l_lean_ir_parse__phi(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_5 = l_lean_ir_parse__var(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = l_lean_ir_parse__typed__assignment___closed__1;
x_14 = l_lean_ir_symbol(x_13, x_8);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_ir_parse__typed__assignment___closed__2;
x_21 = l_lean_ir_str2type;
x_22 = l_lean_ir_parse__key2val___main___rarg(x_20, x_21, x_15);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; 
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_ir_parse__typed__assignment___closed__3;
x_31 = l_lean_ir_symbol(x_30, x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_34; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 2);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_lean_ir_parse__phi___closed__1;
x_38 = l_lean_ir_keyword(x_37, x_32);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 2);
lean::inc(x_41);
lean::dec(x_38);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_6);
lean::cnstr_set(x_44, 1, x_23);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_12;
}
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_39);
lean::cnstr_set(x_46, 2, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_48);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_50);
x_52 = l_lean_parser_parsec__t_try__mk__res___rarg(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_1 = x_53;
x_2 = x_55;
x_3 = x_57;
goto lbl_4;
}
else
{
obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_60 = lean::cnstr_get(x_52, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 x_63 = x_52;
} else {
 lean::inc(x_60);
 lean::dec(x_52);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
return x_65;
}
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_23);
x_69 = lean::cnstr_get(x_38, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_set(x_38, 0, lean::box(0));
 x_72 = x_38;
} else {
 lean::inc(x_69);
 lean::dec(x_38);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_74);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_77);
x_79 = l_lean_parser_parsec__t_try__mk__res___rarg(x_78);
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
x_1 = x_80;
x_2 = x_82;
x_3 = x_84;
goto lbl_4;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_79, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_set(x_79, 0, lean::box(0));
 x_90 = x_79;
} else {
 lean::inc(x_87);
 lean::dec(x_79);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
return x_92;
}
}
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_23);
x_96 = lean::cnstr_get(x_31, 0);
x_98 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_set(x_31, 0, lean::box(0));
 x_99 = x_31;
} else {
 lean::inc(x_96);
 lean::dec(x_31);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_102);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_103);
x_105 = l_lean_parser_parsec__t_try__mk__res___rarg(x_104);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_108; obj* x_110; 
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_105, 2);
lean::inc(x_110);
lean::dec(x_105);
x_1 = x_106;
x_2 = x_108;
x_3 = x_110;
goto lbl_4;
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; 
x_113 = lean::cnstr_get(x_105, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_set(x_105, 0, lean::box(0));
 x_116 = x_105;
} else {
 lean::inc(x_113);
 lean::dec(x_105);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
return x_118;
}
}
}
else
{
obj* x_121; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_12);
lean::dec(x_6);
x_121 = lean::cnstr_get(x_22, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_124 = x_22;
} else {
 lean::inc(x_121);
 lean::dec(x_22);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = x_125;
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_127);
x_129 = l_lean_parser_parsec__t_try__mk__res___rarg(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_132; obj* x_134; 
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_129, 2);
lean::inc(x_134);
lean::dec(x_129);
x_1 = x_130;
x_2 = x_132;
x_3 = x_134;
goto lbl_4;
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; 
x_137 = lean::cnstr_get(x_129, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_129, sizeof(void*)*1);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_set(x_129, 0, lean::box(0));
 x_140 = x_129;
} else {
 lean::inc(x_137);
 lean::dec(x_129);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_139);
x_142 = x_141;
return x_142;
}
}
}
else
{
obj* x_145; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_12);
lean::dec(x_6);
x_145 = lean::cnstr_get(x_14, 0);
x_147 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_148 = x_14;
} else {
 lean::inc(x_145);
 lean::dec(x_14);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_145);
lean::cnstr_set_scalar(x_149, sizeof(void*)*1, x_147);
x_150 = x_149;
x_151 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_150);
x_152 = l_lean_parser_parsec__t_try__mk__res___rarg(x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_155; obj* x_157; 
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_152, 2);
lean::inc(x_157);
lean::dec(x_152);
x_1 = x_153;
x_2 = x_155;
x_3 = x_157;
goto lbl_4;
}
else
{
obj* x_160; uint8 x_162; obj* x_163; obj* x_164; obj* x_165; 
x_160 = lean::cnstr_get(x_152, 0);
x_162 = lean::cnstr_get_scalar<uint8>(x_152, sizeof(void*)*1);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_set(x_152, 0, lean::box(0));
 x_163 = x_152;
} else {
 lean::inc(x_160);
 lean::dec(x_152);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_160);
lean::cnstr_set_scalar(x_164, sizeof(void*)*1, x_162);
x_165 = x_164;
return x_165;
}
}
}
else
{
obj* x_166; obj* x_168; uint8 x_169; obj* x_170; obj* x_171; 
x_166 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_168 = x_5;
} else {
 lean::inc(x_166);
 lean::dec(x_5);
 x_168 = lean::box(0);
}
x_169 = 0;
if (lean::is_scalar(x_168)) {
 x_170 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_170 = x_168;
}
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_169);
x_171 = x_170;
return x_171;
}
lbl_4:
{
obj* x_172; obj* x_174; obj* x_177; 
x_172 = lean::cnstr_get(x_1, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_1, 1);
lean::inc(x_174);
lean::dec(x_1);
x_177 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(x_2);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; obj* x_180; obj* x_182; obj* x_184; obj* x_185; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_178 = lean::cnstr_get(x_177, 0);
x_180 = lean::cnstr_get(x_177, 1);
x_182 = lean::cnstr_get(x_177, 2);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_set(x_177, 0, lean::box(0));
 lean::cnstr_set(x_177, 1, lean::box(0));
 lean::cnstr_set(x_177, 2, lean::box(0));
 x_184 = x_177;
} else {
 lean::inc(x_178);
 lean::inc(x_180);
 lean::inc(x_182);
 lean::dec(x_177);
 x_184 = lean::box(0);
}
x_185 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_185, 0, x_172);
lean::cnstr_set(x_185, 1, x_178);
x_186 = lean::unbox(x_174);
lean::cnstr_set_scalar(x_185, sizeof(void*)*2, x_186);
x_187 = x_185;
x_188 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_184)) {
 x_189 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_189 = x_184;
}
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_180);
lean::cnstr_set(x_189, 2, x_188);
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_189);
x_191 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_190);
return x_191;
}
else
{
obj* x_194; uint8 x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
lean::dec(x_174);
lean::dec(x_172);
x_194 = lean::cnstr_get(x_177, 0);
x_196 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*1);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_set(x_177, 0, lean::box(0));
 x_197 = x_177;
} else {
 lean::inc(x_194);
 lean::dec(x_177);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_194);
lean::cnstr_set_scalar(x_198, sizeof(void*)*1, x_196);
x_199 = x_198;
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_199);
return x_200;
}
}
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(",");
return x_0;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_0);
x_11 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
x_12 = l_lean_ir_symbol(x_11, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 2);
lean::inc(x_15);
lean::dec(x_12);
x_18 = l_lean_ir_parse__blockid(x_13);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_7 = x_20;
x_8 = x_22;
x_9 = x_24;
goto lbl_10;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_5);
x_28 = lean::cnstr_get(x_19, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 x_31 = x_19;
} else {
 lean::inc(x_28);
 lean::dec(x_19);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_5);
x_35 = lean::cnstr_get(x_12, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_38 = x_12;
} else {
 lean::inc(x_35);
 lean::dec(x_12);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
return x_40;
}
lbl_10:
{
obj* x_42; obj* x_43; 
lean::inc(x_8);
x_42 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_5, x_8);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; 
lean::dec(x_8);
x_46 = lean::box(0);
x_43 = x_46;
goto lbl_44;
}
else
{
obj* x_47; uint8 x_49; 
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (x_49 == 0)
{
obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_42);
x_51 = lean::box(0);
x_52 = lean::cnstr_get(x_47, 2);
lean::inc(x_52);
lean::dec(x_47);
x_55 = l_mjoin___rarg___closed__1;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_56, 0, x_52);
lean::closure_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_7);
lean::cnstr_set(x_57, 1, x_51);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_58, 0, x_56);
lean::closure_set(x_58, 1, x_55);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_8);
lean::cnstr_set(x_60, 2, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
else
{
obj* x_64; 
lean::dec(x_8);
lean::dec(x_47);
x_64 = lean::box(0);
x_43 = x_64;
goto lbl_44;
}
}
lbl_44:
{
lean::dec(x_43);
if (lean::obj_tag(x_42) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_66 = lean::cnstr_get(x_42, 0);
x_68 = lean::cnstr_get(x_42, 1);
x_70 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 lean::cnstr_set(x_42, 1, lean::box(0));
 lean::cnstr_set(x_42, 2, lean::box(0));
 x_72 = x_42;
} else {
 lean::inc(x_66);
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_42);
 x_72 = lean::box(0);
}
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_7);
lean::cnstr_set(x_73, 1, x_66);
x_74 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_72)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_72;
}
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_68);
lean::cnstr_set(x_75, 2, x_74);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_76);
return x_77;
}
else
{
obj* x_79; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_7);
x_79 = lean::cnstr_get(x_42, 0);
x_81 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_set(x_42, 0, lean::box(0));
 x_82 = x_42;
} else {
 lean::inc(x_79);
 lean::dec(x_42);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_79);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_81);
x_84 = x_83;
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_84);
return x_85;
}
}
}
}
else
{
obj* x_87; obj* x_88; 
lean::dec(x_0);
x_87 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
x_88 = l_lean_ir_symbol(x_87, x_1);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_93; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_88, 1);
x_91 = lean::cnstr_get(x_88, 2);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_set(x_88, 1, lean::box(0));
 lean::cnstr_set(x_88, 2, lean::box(0));
 x_93 = x_88;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_88);
 x_93 = lean::box(0);
}
x_94 = l_lean_ir_parse__blockid(x_89);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 2);
lean::inc(x_100);
lean::dec(x_95);
x_103 = lean::box(0);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_96);
lean::cnstr_set(x_104, 1, x_103);
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_93)) {
 x_106 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_106 = x_93;
}
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_98);
lean::cnstr_set(x_106, 2, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_106);
return x_107;
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_93);
x_109 = lean::cnstr_get(x_95, 0);
x_111 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_set(x_95, 0, lean::box(0));
 x_112 = x_95;
} else {
 lean::inc(x_109);
 lean::dec(x_95);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
return x_114;
}
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; 
x_115 = lean::cnstr_get(x_88, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_set(x_88, 0, lean::box(0));
 x_118 = x_88;
} else {
 lean::inc(x_115);
 lean::dec(x_88);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
return x_120;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__terminator___spec__3(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__terminator___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__terminator___spec__3(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__blockid(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_sep__by1___rarg___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_2);
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
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
x_17 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 lean::cnstr_set(x_12, 2, lean::box(0));
 x_19 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__terminator___spec__2(x_15);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 2);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::apply_1(x_13, x_21);
if (lean::is_scalar(x_19)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_19;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_23);
lean::cnstr_set(x_29, 2, x_10);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_30);
return x_31;
}
else
{
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_13);
lean::dec(x_19);
x_34 = lean::cnstr_get(x_20, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_37 = x_20;
} else {
 lean::inc(x_34);
 lean::dec(x_20);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_36);
x_39 = x_38;
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_39);
return x_40;
}
}
else
{
obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_12, 0);
x_43 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 x_44 = x_12;
} else {
 lean::inc(x_41);
 lean::dec(x_12);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set_scalar(x_45, sizeof(void*)*1, x_43);
x_46 = x_45;
return x_46;
}
}
else
{
obj* x_47; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_47 = lean::cnstr_get(x_1, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_50 = x_1;
} else {
 lean::inc(x_47);
 lean::dec(x_1);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = x_51;
return x_52;
}
}
}
obj* l_lean_ir_parse__terminator___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_parse__terminator___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("case");
return x_0;
}
}
obj* _init_l_lean_ir_parse__terminator___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ret");
return x_0;
}
}
obj* _init_l_lean_ir_parse__terminator___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("jmp");
return x_0;
}
}
obj* l_lean_ir_parse__terminator(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
x_3 = l_lean_ir_parse__terminator___closed__3;
lean::inc(x_0);
x_5 = l_lean_ir_keyword(x_3, x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 1);
x_8 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = l_lean_ir_parse__blockid(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_11, 2);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_19, 0, x_12);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_10)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_10;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_22);
x_1 = x_23;
goto lbl_2;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_10);
x_25 = lean::cnstr_get(x_11, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_28 = x_11;
} else {
 lean::inc(x_25);
 lean::dec(x_11);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_30);
x_1 = x_31;
goto lbl_2;
}
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_5, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_35 = x_5;
} else {
 lean::inc(x_32);
 lean::dec(x_5);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_1 = x_37;
goto lbl_2;
}
lbl_2:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; uint8 x_44; 
x_39 = lean::cnstr_get(x_1, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_41 == 0)
{
obj* x_47; obj* x_49; 
lean::dec(x_1);
x_47 = l_lean_ir_parse__terminator___closed__2;
lean::inc(x_0);
x_49 = l_lean_ir_keyword(x_47, x_0);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_54; obj* x_55; 
x_50 = lean::cnstr_get(x_49, 1);
x_52 = lean::cnstr_get(x_49, 2);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_set(x_49, 1, lean::box(0));
 lean::cnstr_set(x_49, 2, lean::box(0));
 x_54 = x_49;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_49);
 x_54 = lean::box(0);
}
x_55 = l_lean_ir_parse__var(x_50);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_55, 2);
lean::inc(x_60);
lean::dec(x_55);
x_63 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_63, 0, x_56);
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_54)) {
 x_65 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_65 = x_54;
}
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_58);
lean::cnstr_set(x_65, 2, x_64);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_65);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_66);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; 
lean::dec(x_0);
x_69 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_67);
return x_69;
}
else
{
obj* x_70; uint8 x_72; 
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
x_42 = x_67;
x_43 = x_70;
x_44 = x_72;
goto lbl_45;
}
}
else
{
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_54);
x_74 = lean::cnstr_get(x_55, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_set(x_55, 0, lean::box(0));
 x_77 = x_55;
} else {
 lean::inc(x_74);
 lean::dec(x_55);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_76);
x_79 = x_78;
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; 
lean::dec(x_0);
x_82 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_80);
return x_82;
}
else
{
obj* x_83; uint8 x_85; 
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get_scalar<uint8>(x_80, sizeof(void*)*1);
x_42 = x_80;
x_43 = x_83;
x_44 = x_85;
goto lbl_45;
}
}
}
else
{
obj* x_86; uint8 x_88; obj* x_89; obj* x_91; obj* x_92; 
x_86 = lean::cnstr_get(x_49, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_set(x_49, 0, lean::box(0));
 x_89 = x_49;
} else {
 lean::inc(x_86);
 lean::dec(x_49);
 x_89 = lean::box(0);
}
lean::inc(x_86);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_86);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_88);
x_92 = x_91;
x_42 = x_92;
x_43 = x_86;
x_44 = x_88;
goto lbl_45;
}
}
else
{
lean::dec(x_0);
lean::dec(x_39);
return x_1;
}
lbl_45:
{
obj* x_95; obj* x_96; obj* x_97; 
if (x_44 == 0)
{
obj* x_100; obj* x_101; 
lean::dec(x_42);
x_100 = l_lean_ir_parse__terminator___closed__1;
x_101 = l_lean_ir_keyword(x_100, x_0);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_107; 
x_102 = lean::cnstr_get(x_101, 1);
x_104 = lean::cnstr_get(x_101, 2);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_set(x_101, 1, lean::box(0));
 lean::cnstr_set(x_101, 2, lean::box(0));
 x_106 = x_101;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_101);
 x_106 = lean::box(0);
}
x_107 = l_lean_ir_parse__var(x_102);
if (lean::obj_tag(x_107) == 0)
{
obj* x_108; obj* x_110; obj* x_112; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_107, 2);
lean::inc(x_112);
lean::dec(x_107);
x_115 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__terminator___lambda__1), 2, 1);
lean::closure_set(x_115, 0, x_108);
x_116 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_106)) {
 x_117 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_117 = x_106;
}
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_110);
lean::cnstr_set(x_117, 2, x_116);
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_104, x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_120; obj* x_122; obj* x_124; 
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_119, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_119, 2);
lean::inc(x_124);
lean::dec(x_119);
x_95 = x_120;
x_96 = x_122;
x_97 = x_124;
goto lbl_98;
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_127 = lean::cnstr_get(x_119, 0);
x_129 = lean::cnstr_get_scalar<uint8>(x_119, sizeof(void*)*1);
if (lean::is_exclusive(x_119)) {
 lean::cnstr_set(x_119, 0, lean::box(0));
 x_130 = x_119;
} else {
 lean::inc(x_127);
 lean::dec(x_119);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_129);
x_132 = x_131;
x_133 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_132);
x_134 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_133);
return x_134;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_106);
x_136 = lean::cnstr_get(x_107, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_107, sizeof(void*)*1);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_set(x_107, 0, lean::box(0));
 x_139 = x_107;
} else {
 lean::inc(x_136);
 lean::dec(x_107);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_136);
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_138);
x_141 = x_140;
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_104, x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_145; obj* x_147; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_142, 2);
lean::inc(x_147);
lean::dec(x_142);
x_95 = x_143;
x_96 = x_145;
x_97 = x_147;
goto lbl_98;
}
else
{
obj* x_150; uint8 x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_150 = lean::cnstr_get(x_142, 0);
x_152 = lean::cnstr_get_scalar<uint8>(x_142, sizeof(void*)*1);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_set(x_142, 0, lean::box(0));
 x_153 = x_142;
} else {
 lean::inc(x_150);
 lean::dec(x_142);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_150);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = x_154;
x_156 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_155);
x_157 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_156);
return x_157;
}
}
}
else
{
obj* x_158; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_158 = lean::cnstr_get(x_101, 0);
x_160 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_set(x_101, 0, lean::box(0));
 x_161 = x_101;
} else {
 lean::inc(x_158);
 lean::dec(x_101);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_160);
x_163 = x_162;
x_164 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_163);
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_164);
return x_165;
}
}
else
{
obj* x_168; 
lean::dec(x_0);
lean::dec(x_43);
x_168 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_42);
return x_168;
}
lbl_98:
{
obj* x_169; obj* x_170; obj* x_171; obj* x_173; obj* x_174; 
x_173 = l_list_repr___main___rarg___closed__2;
x_174 = l_lean_ir_symbol(x_173, x_96);
if (lean::obj_tag(x_174) == 0)
{
obj* x_175; obj* x_177; obj* x_180; obj* x_181; 
x_175 = lean::cnstr_get(x_174, 1);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 2);
lean::inc(x_177);
lean::dec(x_174);
x_180 = l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(x_175);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_177, x_180);
if (lean::obj_tag(x_181) == 0)
{
obj* x_182; obj* x_184; obj* x_186; 
x_182 = lean::cnstr_get(x_181, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_181, 2);
lean::inc(x_186);
lean::dec(x_181);
x_169 = x_182;
x_170 = x_184;
x_171 = x_186;
goto lbl_172;
}
else
{
obj* x_190; uint8 x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_95);
x_190 = lean::cnstr_get(x_181, 0);
x_192 = lean::cnstr_get_scalar<uint8>(x_181, sizeof(void*)*1);
if (lean::is_exclusive(x_181)) {
 lean::cnstr_set(x_181, 0, lean::box(0));
 x_193 = x_181;
} else {
 lean::inc(x_190);
 lean::dec(x_181);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_190);
lean::cnstr_set_scalar(x_194, sizeof(void*)*1, x_192);
x_195 = x_194;
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_195);
x_197 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_196);
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_197);
return x_198;
}
}
else
{
obj* x_200; uint8 x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_95);
x_200 = lean::cnstr_get(x_174, 0);
x_202 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_set(x_174, 0, lean::box(0));
 x_203 = x_174;
} else {
 lean::inc(x_200);
 lean::dec(x_174);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_200);
lean::cnstr_set_scalar(x_204, sizeof(void*)*1, x_202);
x_205 = x_204;
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_205);
x_207 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_206);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_207);
return x_208;
}
lbl_172:
{
obj* x_209; obj* x_210; 
x_209 = l_list_repr___main___rarg___closed__3;
x_210 = l_lean_ir_symbol(x_209, x_170);
if (lean::obj_tag(x_210) == 0)
{
obj* x_211; obj* x_213; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
x_211 = lean::cnstr_get(x_210, 1);
x_213 = lean::cnstr_get(x_210, 2);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_release(x_210, 0);
 lean::cnstr_set(x_210, 1, lean::box(0));
 lean::cnstr_set(x_210, 2, lean::box(0));
 x_215 = x_210;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::dec(x_210);
 x_215 = lean::box(0);
}
x_216 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_215)) {
 x_217 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_217 = x_215;
}
lean::cnstr_set(x_217, 0, x_169);
lean::cnstr_set(x_217, 1, x_211);
lean::cnstr_set(x_217, 2, x_216);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_213, x_217);
x_219 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_218);
if (lean::obj_tag(x_219) == 0)
{
obj* x_220; obj* x_222; obj* x_224; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
x_220 = lean::cnstr_get(x_219, 0);
x_222 = lean::cnstr_get(x_219, 1);
x_224 = lean::cnstr_get(x_219, 2);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_set(x_219, 0, lean::box(0));
 lean::cnstr_set(x_219, 1, lean::box(0));
 lean::cnstr_set(x_219, 2, lean::box(0));
 x_226 = x_219;
} else {
 lean::inc(x_220);
 lean::inc(x_222);
 lean::inc(x_224);
 lean::dec(x_219);
 x_226 = lean::box(0);
}
x_227 = lean::apply_1(x_95, x_220);
if (lean::is_scalar(x_226)) {
 x_228 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_228 = x_226;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_222);
lean::cnstr_set(x_228, 2, x_216);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_224, x_228);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_229);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_231);
return x_232;
}
else
{
obj* x_234; uint8 x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_95);
x_234 = lean::cnstr_get(x_219, 0);
x_236 = lean::cnstr_get_scalar<uint8>(x_219, sizeof(void*)*1);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_set(x_219, 0, lean::box(0));
 x_237 = x_219;
} else {
 lean::inc(x_234);
 lean::dec(x_219);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_234);
lean::cnstr_set_scalar(x_238, sizeof(void*)*1, x_236);
x_239 = x_238;
x_240 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_239);
x_241 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_240);
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_241);
return x_242;
}
}
else
{
obj* x_244; uint8 x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_169);
x_244 = lean::cnstr_get(x_210, 0);
x_246 = lean::cnstr_get_scalar<uint8>(x_210, sizeof(void*)*1);
if (lean::is_exclusive(x_210)) {
 lean::cnstr_set(x_210, 0, lean::box(0));
 x_247 = x_210;
} else {
 lean::inc(x_244);
 lean::dec(x_210);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_244);
lean::cnstr_set_scalar(x_248, sizeof(void*)*1, x_246);
x_249 = x_248;
x_250 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_249);
if (lean::obj_tag(x_250) == 0)
{
obj* x_251; obj* x_253; obj* x_255; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
x_251 = lean::cnstr_get(x_250, 0);
x_253 = lean::cnstr_get(x_250, 1);
x_255 = lean::cnstr_get(x_250, 2);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_set(x_250, 0, lean::box(0));
 lean::cnstr_set(x_250, 1, lean::box(0));
 lean::cnstr_set(x_250, 2, lean::box(0));
 x_257 = x_250;
} else {
 lean::inc(x_251);
 lean::inc(x_253);
 lean::inc(x_255);
 lean::dec(x_250);
 x_257 = lean::box(0);
}
x_258 = lean::apply_1(x_95, x_251);
x_259 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_257)) {
 x_260 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_260 = x_257;
}
lean::cnstr_set(x_260, 0, x_258);
lean::cnstr_set(x_260, 1, x_253);
lean::cnstr_set(x_260, 2, x_259);
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_255, x_260);
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_261);
x_263 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_262);
x_264 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_263);
return x_264;
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_95);
x_266 = lean::cnstr_get(x_250, 0);
x_268 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*1);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_set(x_250, 0, lean::box(0));
 x_269 = x_250;
} else {
 lean::inc(x_266);
 lean::dec(x_250);
 x_269 = lean::box(0);
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_271);
x_273 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_272);
x_274 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_273);
return x_274;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(";");
return x_0;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_0);
x_11 = l_lean_ir_parse__phi(x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_11, 0);
x_14 = lean::cnstr_get(x_11, 1);
x_16 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_18 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_20 = l_lean_ir_symbol(x_19, x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_18;
}
lean::cnstr_set(x_27, 0, x_12);
lean::cnstr_set(x_27, 1, x_21);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_32; obj* x_34; 
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 2);
lean::inc(x_34);
lean::dec(x_29);
x_7 = x_30;
x_8 = x_32;
x_9 = x_34;
goto lbl_10;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_5);
x_38 = lean::cnstr_get(x_29, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 x_41 = x_29;
} else {
 lean::inc(x_38);
 lean::dec(x_29);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
return x_43;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_12);
lean::dec(x_18);
x_46 = lean::cnstr_get(x_20, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_49 = x_20;
} else {
 lean::inc(x_46);
 lean::dec(x_20);
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
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_7 = x_53;
x_8 = x_55;
x_9 = x_57;
goto lbl_10;
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_5);
x_61 = lean::cnstr_get(x_52, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 x_64 = x_52;
} else {
 lean::inc(x_61);
 lean::dec(x_52);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
return x_66;
}
}
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_5);
x_68 = lean::cnstr_get(x_11, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_71 = x_11;
} else {
 lean::inc(x_68);
 lean::dec(x_11);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
return x_73;
}
lbl_10:
{
obj* x_75; obj* x_76; 
lean::inc(x_8);
x_75 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_5, x_8);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; 
lean::dec(x_8);
x_79 = lean::box(0);
x_76 = x_79;
goto lbl_77;
}
else
{
obj* x_80; uint8 x_82; 
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_75);
x_84 = lean::box(0);
x_85 = lean::cnstr_get(x_80, 2);
lean::inc(x_85);
lean::dec(x_80);
x_88 = l_mjoin___rarg___closed__1;
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_89, 0, x_85);
lean::closure_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_7);
lean::cnstr_set(x_90, 1, x_84);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_91, 0, x_89);
lean::closure_set(x_91, 1, x_88);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_8);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_93);
return x_94;
}
else
{
obj* x_97; 
lean::dec(x_80);
lean::dec(x_8);
x_97 = lean::box(0);
x_76 = x_97;
goto lbl_77;
}
}
lbl_77:
{
lean::dec(x_76);
if (lean::obj_tag(x_75) == 0)
{
obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_75, 0);
x_101 = lean::cnstr_get(x_75, 1);
x_103 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 lean::cnstr_set(x_75, 2, lean::box(0));
 x_105 = x_75;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_75);
 x_105 = lean::box(0);
}
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_7);
lean::cnstr_set(x_106, 1, x_99);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_105)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_105;
}
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_101);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_109);
return x_110;
}
else
{
obj* x_112; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_7);
x_112 = lean::cnstr_get(x_75, 0);
x_114 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 x_115 = x_75;
} else {
 lean::inc(x_112);
 lean::dec(x_75);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = x_116;
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_117);
return x_118;
}
}
}
}
else
{
obj* x_120; 
lean::dec(x_0);
x_120 = l_lean_ir_parse__phi(x_1);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_128; obj* x_129; 
x_121 = lean::cnstr_get(x_120, 0);
x_123 = lean::cnstr_get(x_120, 1);
x_125 = lean::cnstr_get(x_120, 2);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_set(x_120, 0, lean::box(0));
 lean::cnstr_set(x_120, 1, lean::box(0));
 lean::cnstr_set(x_120, 2, lean::box(0));
 x_127 = x_120;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::inc(x_125);
 lean::dec(x_120);
 x_127 = lean::box(0);
}
x_128 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_129 = l_lean_ir_symbol(x_128, x_123);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_130 = lean::cnstr_get(x_129, 1);
x_132 = lean::cnstr_get(x_129, 2);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_set(x_129, 1, lean::box(0));
 lean::cnstr_set(x_129, 2, lean::box(0));
 x_134 = x_129;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_129);
 x_134 = lean::box(0);
}
x_135 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_136 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_136 = x_127;
}
lean::cnstr_set(x_136, 0, x_121);
lean::cnstr_set(x_136, 1, x_130);
lean::cnstr_set(x_136, 2, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_132, x_136);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_138, 2);
lean::inc(x_143);
lean::dec(x_138);
x_146 = lean::box(0);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_139);
lean::cnstr_set(x_147, 1, x_146);
if (lean::is_scalar(x_134)) {
 x_148 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_148 = x_134;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_141);
lean::cnstr_set(x_148, 2, x_135);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_143, x_148);
return x_149;
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
x_151 = lean::cnstr_get(x_138, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_138, sizeof(void*)*1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_set(x_138, 0, lean::box(0));
 x_154 = x_138;
} else {
 lean::inc(x_151);
 lean::dec(x_138);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set_scalar(x_155, sizeof(void*)*1, x_153);
x_156 = x_155;
return x_156;
}
}
else
{
obj* x_158; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_121);
x_158 = lean::cnstr_get(x_129, 0);
x_160 = lean::cnstr_get_scalar<uint8>(x_129, sizeof(void*)*1);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_set(x_129, 0, lean::box(0));
 x_161 = x_129;
} else {
 lean::inc(x_158);
 lean::dec(x_129);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_160);
x_163 = x_162;
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_163);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_167; obj* x_169; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 2);
lean::inc(x_169);
lean::dec(x_164);
x_172 = lean::box(0);
x_173 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_173, 0, x_165);
lean::cnstr_set(x_173, 1, x_172);
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_175 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_175 = x_127;
}
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set(x_175, 1, x_167);
lean::cnstr_set(x_175, 2, x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_175);
return x_176;
}
else
{
obj* x_178; uint8 x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_127);
x_178 = lean::cnstr_get(x_164, 0);
x_180 = lean::cnstr_get_scalar<uint8>(x_164, sizeof(void*)*1);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_set(x_164, 0, lean::box(0));
 x_181 = x_164;
} else {
 lean::inc(x_178);
 lean::dec(x_164);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_178);
lean::cnstr_set_scalar(x_182, sizeof(void*)*1, x_180);
x_183 = x_182;
return x_183;
}
}
}
else
{
obj* x_184; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; 
x_184 = lean::cnstr_get(x_120, 0);
x_186 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_set(x_120, 0, lean::box(0));
 x_187 = x_120;
} else {
 lean::inc(x_184);
 lean::dec(x_120);
 x_187 = lean::box(0);
}
if (lean::is_scalar(x_187)) {
 x_188 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_188 = x_187;
}
lean::cnstr_set(x_188, 0, x_184);
lean::cnstr_set_scalar(x_188, sizeof(void*)*1, x_186);
x_189 = x_188;
return x_189;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_0);
x_11 = l_lean_ir_parse__instr(x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_11, 0);
x_14 = lean::cnstr_get(x_11, 1);
x_16 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_18 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_20 = l_lean_ir_symbol(x_19, x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_18;
}
lean::cnstr_set(x_27, 0, x_12);
lean::cnstr_set(x_27, 1, x_21);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_32; obj* x_34; 
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 2);
lean::inc(x_34);
lean::dec(x_29);
x_7 = x_30;
x_8 = x_32;
x_9 = x_34;
goto lbl_10;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_5);
x_38 = lean::cnstr_get(x_29, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_set(x_29, 0, lean::box(0));
 x_41 = x_29;
} else {
 lean::inc(x_38);
 lean::dec(x_29);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
return x_43;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_12);
lean::dec(x_18);
x_46 = lean::cnstr_get(x_20, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_49 = x_20;
} else {
 lean::inc(x_46);
 lean::dec(x_20);
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
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_7 = x_53;
x_8 = x_55;
x_9 = x_57;
goto lbl_10;
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_5);
x_61 = lean::cnstr_get(x_52, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 x_64 = x_52;
} else {
 lean::inc(x_61);
 lean::dec(x_52);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
return x_66;
}
}
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_5);
x_68 = lean::cnstr_get(x_11, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_71 = x_11;
} else {
 lean::inc(x_68);
 lean::dec(x_11);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
return x_73;
}
lbl_10:
{
obj* x_75; obj* x_76; 
lean::inc(x_8);
x_75 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(x_5, x_8);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; 
lean::dec(x_8);
x_79 = lean::box(0);
x_76 = x_79;
goto lbl_77;
}
else
{
obj* x_80; uint8 x_82; 
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_75);
x_84 = lean::box(0);
x_85 = lean::cnstr_get(x_80, 2);
lean::inc(x_85);
lean::dec(x_80);
x_88 = l_mjoin___rarg___closed__1;
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_89, 0, x_85);
lean::closure_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_7);
lean::cnstr_set(x_90, 1, x_84);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_91, 0, x_89);
lean::closure_set(x_91, 1, x_88);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_8);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_93);
return x_94;
}
else
{
obj* x_97; 
lean::dec(x_80);
lean::dec(x_8);
x_97 = lean::box(0);
x_76 = x_97;
goto lbl_77;
}
}
lbl_77:
{
lean::dec(x_76);
if (lean::obj_tag(x_75) == 0)
{
obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_75, 0);
x_101 = lean::cnstr_get(x_75, 1);
x_103 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 lean::cnstr_set(x_75, 2, lean::box(0));
 x_105 = x_75;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_75);
 x_105 = lean::box(0);
}
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_7);
lean::cnstr_set(x_106, 1, x_99);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_105)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_105;
}
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_101);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_109);
return x_110;
}
else
{
obj* x_112; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_7);
x_112 = lean::cnstr_get(x_75, 0);
x_114 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 x_115 = x_75;
} else {
 lean::inc(x_112);
 lean::dec(x_75);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = x_116;
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_117);
return x_118;
}
}
}
}
else
{
obj* x_120; 
lean::dec(x_0);
x_120 = l_lean_ir_parse__instr(x_1);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_123; obj* x_125; obj* x_127; obj* x_128; obj* x_129; 
x_121 = lean::cnstr_get(x_120, 0);
x_123 = lean::cnstr_get(x_120, 1);
x_125 = lean::cnstr_get(x_120, 2);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_set(x_120, 0, lean::box(0));
 lean::cnstr_set(x_120, 1, lean::box(0));
 lean::cnstr_set(x_120, 2, lean::box(0));
 x_127 = x_120;
} else {
 lean::inc(x_121);
 lean::inc(x_123);
 lean::inc(x_125);
 lean::dec(x_120);
 x_127 = lean::box(0);
}
x_128 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_129 = l_lean_ir_symbol(x_128, x_123);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_130 = lean::cnstr_get(x_129, 1);
x_132 = lean::cnstr_get(x_129, 2);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_set(x_129, 1, lean::box(0));
 lean::cnstr_set(x_129, 2, lean::box(0));
 x_134 = x_129;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_129);
 x_134 = lean::box(0);
}
x_135 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_136 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_136 = x_127;
}
lean::cnstr_set(x_136, 0, x_121);
lean::cnstr_set(x_136, 1, x_130);
lean::cnstr_set(x_136, 2, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_132, x_136);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_138, 2);
lean::inc(x_143);
lean::dec(x_138);
x_146 = lean::box(0);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_139);
lean::cnstr_set(x_147, 1, x_146);
if (lean::is_scalar(x_134)) {
 x_148 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_148 = x_134;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_141);
lean::cnstr_set(x_148, 2, x_135);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_143, x_148);
return x_149;
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
x_151 = lean::cnstr_get(x_138, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_138, sizeof(void*)*1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_set(x_138, 0, lean::box(0));
 x_154 = x_138;
} else {
 lean::inc(x_151);
 lean::dec(x_138);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set_scalar(x_155, sizeof(void*)*1, x_153);
x_156 = x_155;
return x_156;
}
}
else
{
obj* x_158; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_121);
x_158 = lean::cnstr_get(x_129, 0);
x_160 = lean::cnstr_get_scalar<uint8>(x_129, sizeof(void*)*1);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_set(x_129, 0, lean::box(0));
 x_161 = x_129;
} else {
 lean::inc(x_158);
 lean::dec(x_129);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_160);
x_163 = x_162;
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_163);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_167; obj* x_169; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_164, 2);
lean::inc(x_169);
lean::dec(x_164);
x_172 = lean::box(0);
x_173 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_173, 0, x_165);
lean::cnstr_set(x_173, 1, x_172);
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_175 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_175 = x_127;
}
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set(x_175, 1, x_167);
lean::cnstr_set(x_175, 2, x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_175);
return x_176;
}
else
{
obj* x_178; uint8 x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_127);
x_178 = lean::cnstr_get(x_164, 0);
x_180 = lean::cnstr_get_scalar<uint8>(x_164, sizeof(void*)*1);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_set(x_164, 0, lean::box(0));
 x_181 = x_164;
} else {
 lean::inc(x_178);
 lean::dec(x_164);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_178);
lean::cnstr_set_scalar(x_182, sizeof(void*)*1, x_180);
x_183 = x_182;
return x_183;
}
}
}
else
{
obj* x_184; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; 
x_184 = lean::cnstr_get(x_120, 0);
x_186 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_set(x_120, 0, lean::box(0));
 x_187 = x_120;
} else {
 lean::inc(x_184);
 lean::dec(x_120);
 x_187 = lean::box(0);
}
if (lean::is_scalar(x_187)) {
 x_188 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_188 = x_187;
}
lean::cnstr_set(x_188, 0, x_184);
lean::cnstr_set_scalar(x_188, sizeof(void*)*1, x_186);
x_189 = x_188;
return x_189;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__5(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__5(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_ir_parse__block(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_5 = l_lean_ir_parse__blockid(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = l_lean_ir_parse__typed__assignment___closed__1;
x_14 = l_lean_ir_symbol(x_13, x_8);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_12;
}
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_22);
x_24 = l_lean_parser_parsec__t_try__mk__res___rarg(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 2);
lean::inc(x_29);
lean::dec(x_24);
x_1 = x_25;
x_2 = x_27;
x_3 = x_29;
goto lbl_4;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_24, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_35 = x_24;
} else {
 lean::inc(x_32);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
return x_37;
}
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_12);
lean::dec(x_6);
x_40 = lean::cnstr_get(x_14, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_43 = x_14;
} else {
 lean::inc(x_40);
 lean::dec(x_14);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = x_44;
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_45);
x_47 = l_lean_parser_parsec__t_try__mk__res___rarg(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_50; obj* x_52; 
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 2);
lean::inc(x_52);
lean::dec(x_47);
x_1 = x_48;
x_2 = x_50;
x_3 = x_52;
goto lbl_4;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_47, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_set(x_47, 0, lean::box(0));
 x_58 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
return x_60;
}
}
}
else
{
obj* x_61; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 x_63 = x_5;
} else {
 lean::inc(x_61);
 lean::dec(x_5);
 x_63 = lean::box(0);
}
x_64 = 0;
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_64);
x_66 = x_65;
return x_66;
}
lbl_4:
{
obj* x_67; 
x_67 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(x_2);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 lean::cnstr_set(x_67, 1, lean::box(0));
 lean::cnstr_set(x_67, 2, lean::box(0));
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
x_76 = lean::cnstr_get(x_75, 0);
x_78 = lean::cnstr_get(x_75, 1);
x_80 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 lean::cnstr_set(x_75, 1, lean::box(0));
 lean::cnstr_set(x_75, 2, lean::box(0));
 x_82 = x_75;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = l_lean_ir_parse__terminator(x_78);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 2);
lean::inc(x_88);
lean::dec(x_83);
x_91 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_92 = l_lean_ir_symbol(x_91, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_95; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 2);
lean::inc(x_95);
lean::dec(x_92);
x_98 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_99 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_99 = x_74;
}
lean::cnstr_set(x_99, 0, x_84);
lean::cnstr_set(x_99, 1, x_93);
lean::cnstr_set(x_99, 2, x_98);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_101, 2);
lean::inc(x_106);
lean::dec(x_101);
x_109 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_109, 0, x_1);
lean::cnstr_set(x_109, 1, x_68);
lean::cnstr_set(x_109, 2, x_76);
lean::cnstr_set(x_109, 3, x_102);
if (lean::is_scalar(x_82)) {
 x_110 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_110 = x_82;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_104);
lean::cnstr_set(x_110, 2, x_98);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_106, x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_111);
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_112);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_113);
return x_114;
}
else
{
obj* x_119; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_82);
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_68);
x_119 = lean::cnstr_get(x_101, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_set(x_101, 0, lean::box(0));
 x_122 = x_101;
} else {
 lean::inc(x_119);
 lean::dec(x_101);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_121);
x_124 = x_123;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_124);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_126);
return x_127;
}
}
else
{
obj* x_130; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_82);
lean::dec(x_84);
x_130 = lean::cnstr_get(x_92, 0);
x_132 = lean::cnstr_get_scalar<uint8>(x_92, sizeof(void*)*1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_set(x_92, 0, lean::box(0));
 x_133 = x_92;
} else {
 lean::inc(x_130);
 lean::dec(x_92);
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
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_136, 2);
lean::inc(x_141);
lean::dec(x_136);
x_144 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_144, 0, x_1);
lean::cnstr_set(x_144, 1, x_68);
lean::cnstr_set(x_144, 2, x_76);
lean::cnstr_set(x_144, 3, x_137);
x_145 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_146 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_146 = x_74;
}
lean::cnstr_set(x_146, 0, x_144);
lean::cnstr_set(x_146, 1, x_139);
lean::cnstr_set(x_146, 2, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_141, x_146);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_147);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_148);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_149);
return x_150;
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_74);
lean::dec(x_68);
x_155 = lean::cnstr_get(x_136, 0);
x_157 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_set(x_136, 0, lean::box(0));
 x_158 = x_136;
} else {
 lean::inc(x_155);
 lean::dec(x_136);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_155);
lean::cnstr_set_scalar(x_159, sizeof(void*)*1, x_157);
x_160 = x_159;
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_160);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_161);
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_162);
return x_163;
}
}
}
else
{
obj* x_169; uint8 x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_82);
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_74);
lean::dec(x_68);
x_169 = lean::cnstr_get(x_83, 0);
x_171 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_set(x_83, 0, lean::box(0));
 x_172 = x_83;
} else {
 lean::inc(x_169);
 lean::dec(x_83);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_169);
lean::cnstr_set_scalar(x_173, sizeof(void*)*1, x_171);
x_174 = x_173;
x_175 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_175);
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_176);
return x_177;
}
}
else
{
obj* x_181; uint8 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
lean::dec(x_1);
lean::dec(x_74);
lean::dec(x_68);
x_181 = lean::cnstr_get(x_75, 0);
x_183 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_set(x_75, 0, lean::box(0));
 x_184 = x_75;
} else {
 lean::inc(x_181);
 lean::dec(x_75);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_181);
lean::cnstr_set_scalar(x_185, sizeof(void*)*1, x_183);
x_186 = x_185;
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_186);
x_188 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_187);
return x_188;
}
}
else
{
obj* x_190; uint8 x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_1);
x_190 = lean::cnstr_get(x_67, 0);
x_192 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 x_193 = x_67;
} else {
 lean::inc(x_190);
 lean::dec(x_67);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_190);
lean::cnstr_set_scalar(x_194, sizeof(void*)*1, x_192);
x_195 = x_194;
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_195);
return x_196;
}
}
}
}
obj* l_lean_ir_parse__arg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_prod_has__repr___rarg___closed__1;
x_2 = l_lean_ir_symbol(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_lean_ir_parse__var(x_3);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_ir_parse__typed__assignment___closed__1;
x_17 = l_lean_ir_symbol(x_16, x_11);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_ir_parse__typed__assignment___closed__2;
x_24 = l_lean_ir_str2type;
x_25 = l_lean_ir_parse__key2val___main___rarg(x_23, x_24, x_18);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; obj* x_33; obj* x_34; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 2);
lean::inc(x_30);
lean::dec(x_25);
x_33 = l_option_has__repr___rarg___closed__3;
x_34 = l_lean_ir_symbol(x_33, x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 2);
lean::inc(x_37);
lean::dec(x_34);
x_40 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_40, 0, x_9);
x_41 = lean::unbox(x_26);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_41);
x_42 = x_40;
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_7)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_7;
}
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_35);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_44);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_48);
return x_49;
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_7);
lean::dec(x_26);
lean::dec(x_9);
x_53 = lean::cnstr_get(x_34, 0);
x_55 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_set(x_34, 0, lean::box(0));
 x_56 = x_34;
} else {
 lean::inc(x_53);
 lean::dec(x_34);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_61);
return x_62;
}
}
else
{
obj* x_65; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_7);
lean::dec(x_9);
x_65 = lean::cnstr_get(x_25, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 x_68 = x_25;
} else {
 lean::inc(x_65);
 lean::dec(x_25);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_67);
x_70 = x_69;
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_70);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_72);
return x_73;
}
}
else
{
obj* x_76; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_7);
lean::dec(x_9);
x_76 = lean::cnstr_get(x_17, 0);
x_78 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_79 = x_17;
} else {
 lean::inc(x_76);
 lean::dec(x_17);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_82);
return x_83;
}
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_7);
x_85 = lean::cnstr_get(x_8, 0);
x_87 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_88 = x_8;
} else {
 lean::inc(x_85);
 lean::dec(x_8);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_90);
return x_91;
}
}
else
{
obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; 
x_92 = lean::cnstr_get(x_2, 0);
x_94 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_95 = x_2;
} else {
 lean::inc(x_92);
 lean::dec(x_2);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
return x_97;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__arg(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__arg(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__header___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__header___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__header___spec__2(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_ir_parse__header(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_parse__fnid(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
if (x_0 == 0)
{
obj* x_16; 
x_16 = lean::box(0);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::box(0);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_10 = x_17;
x_11 = x_5;
x_12 = x_18;
goto lbl_13;
}
lbl_13:
{
obj* x_19; obj* x_20; 
x_19 = l_lean_ir_parse__typed__assignment___closed__1;
x_20 = l_lean_ir_symbol(x_19, x_11);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_20, 1);
x_23 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_set(x_20, 1, lean::box(0));
 lean::cnstr_set(x_20, 2, lean::box(0));
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = l_lean_ir_parse__typed__assignment___closed__2;
x_27 = l_lean_ir_str2type;
x_28 = l_lean_ir_parse__key2val___main___rarg(x_26, x_27, x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 2);
lean::inc(x_33);
lean::dec(x_28);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_9)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_9;
}
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set(x_37, 1, x_31);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_37);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 2);
lean::inc(x_44);
lean::dec(x_39);
x_47 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_47, 0, x_3);
lean::cnstr_set(x_47, 1, x_10);
lean::cnstr_set(x_47, 2, x_40);
lean::cnstr_set_scalar(x_47, sizeof(void*)*3, x_0);
x_48 = x_47;
if (lean::is_scalar(x_25)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_25;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_42);
lean::cnstr_set(x_49, 2, x_36);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_51);
return x_52;
}
else
{
obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_3);
lean::dec(x_25);
lean::dec(x_10);
x_56 = lean::cnstr_get(x_39, 0);
x_58 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_set(x_39, 0, lean::box(0));
 x_59 = x_39;
} else {
 lean::inc(x_56);
 lean::dec(x_39);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_58);
x_61 = x_60;
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_61);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_62);
return x_63;
}
}
else
{
obj* x_65; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_25);
x_65 = lean::cnstr_get(x_28, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 x_68 = x_28;
} else {
 lean::inc(x_65);
 lean::dec(x_28);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_67);
x_70 = x_69;
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 2);
lean::inc(x_76);
lean::dec(x_71);
x_79 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_79, 0, x_3);
lean::cnstr_set(x_79, 1, x_10);
lean::cnstr_set(x_79, 2, x_72);
lean::cnstr_set_scalar(x_79, sizeof(void*)*3, x_0);
x_80 = x_79;
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_9)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_9;
}
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_74);
lean::cnstr_set(x_82, 2, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_84);
return x_85;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_10);
x_89 = lean::cnstr_get(x_71, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_set(x_71, 0, lean::box(0));
 x_92 = x_71;
} else {
 lean::inc(x_89);
 lean::dec(x_71);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_95);
return x_96;
}
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_10);
x_100 = lean::cnstr_get(x_20, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 x_103 = x_20;
} else {
 lean::inc(x_100);
 lean::dec(x_20);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_106);
return x_107;
}
}
lbl_15:
{
obj* x_109; 
lean::dec(x_14);
x_109 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__header___spec__1(x_5);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_114; 
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 2);
lean::inc(x_114);
lean::dec(x_109);
x_10 = x_110;
x_11 = x_112;
x_12 = x_114;
goto lbl_13;
}
else
{
obj* x_119; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_9);
lean::dec(x_3);
x_119 = lean::cnstr_get(x_109, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_set(x_109, 0, lean::box(0));
 x_122 = x_109;
} else {
 lean::inc(x_119);
 lean::dec(x_109);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_121);
x_124 = x_123;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_124);
return x_125;
}
}
}
else
{
obj* x_126; uint8 x_128; obj* x_129; obj* x_130; obj* x_131; 
x_126 = lean::cnstr_get(x_2, 0);
x_128 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_129 = x_2;
} else {
 lean::inc(x_126);
 lean::dec(x_2);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set_scalar(x_130, sizeof(void*)*1, x_128);
x_131 = x_130;
return x_131;
}
}
}
obj* l_lean_ir_parse__header___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_lean_ir_parse__header(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l_lean_ir_parse__def___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_parse__def___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("def");
return x_0;
}
}
obj* l_lean_ir_parse__def(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_5 = l_lean_ir_parse__def___closed__1;
x_6 = l_lean_ir_keyword(x_5, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; uint8 x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_6, 1);
x_9 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = 0;
x_13 = l_lean_ir_parse__header(x_12, x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 2);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_14);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_16);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 2);
lean::inc(x_30);
lean::dec(x_25);
x_1 = x_26;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_25, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 x_36 = x_25;
} else {
 lean::inc(x_33);
 lean::dec(x_25);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_11);
x_40 = lean::cnstr_get(x_13, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_43 = x_13;
} else {
 lean::inc(x_40);
 lean::dec(x_13);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = x_44;
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_1 = x_47;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_46, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 x_57 = x_46;
} else {
 lean::inc(x_54);
 lean::dec(x_46);
 x_57 = lean::box(0);
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
}
else
{
obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_60 = lean::cnstr_get(x_6, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_63 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
return x_65;
}
lbl_4:
{
obj* x_66; obj* x_67; 
x_66 = l_lean_ir_parse__typed__assignment___closed__3;
x_67 = l_lean_ir_symbol(x_66, x_2);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_68 = lean::cnstr_get(x_67, 1);
x_70 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_set(x_67, 1, lean::box(0));
 lean::cnstr_set(x_67, 2, lean::box(0));
 x_72 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_67);
 x_72 = lean::box(0);
}
x_73 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(x_68);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 2);
lean::inc(x_79);
lean::dec(x_74);
x_82 = lean::apply_1(x_1, x_75);
x_83 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_72)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_72;
}
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_77);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_85);
return x_86;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_1);
lean::dec(x_72);
x_89 = lean::cnstr_get(x_74, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_set(x_74, 0, lean::box(0));
 x_92 = x_74;
} else {
 lean::inc(x_89);
 lean::dec(x_74);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_94);
return x_95;
}
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_1);
x_97 = lean::cnstr_get(x_67, 0);
x_99 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 x_100 = x_67;
} else {
 lean::inc(x_97);
 lean::dec(x_67);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_102);
return x_103;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
lean::inc(x_7);
x_16 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_13, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_7);
x_20 = lean::box(0);
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_11);
lean::dec(x_16);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_26);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_33, 0, x_31);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_39; 
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_17 = x_39;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_16) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_16, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_16, 2);
lean::inc(x_45);
lean::dec(x_16);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_43);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_51);
return x_52;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_11);
lean::dec(x_5);
x_55 = lean::cnstr_get(x_16, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_set(x_16, 0, lean::box(0));
 x_58 = x_16;
} else {
 lean::inc(x_55);
 lean::dec(x_16);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_60);
return x_61;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_63 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_66 = x_4;
} else {
 lean::inc(x_63);
 lean::dec(x_4);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
x_75 = lean::cnstr_get(x_70, 2);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 lean::cnstr_set(x_70, 1, lean::box(0));
 lean::cnstr_set(x_70, 2, lean::box(0));
 x_77 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_73);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_81);
return x_82;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_70, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_set(x_70, 0, lean::box(0));
 x_86 = x_70;
} else {
 lean::inc(x_83);
 lean::dec(x_70);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
return x_88;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_1, x_0);
x_3 = l_lean_ir_keyword___closed__1;
x_4 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_2);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_13, 0, x_9);
lean::closure_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* _init_l_lean_ir_parse__defconst___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("defconst");
return x_0;
}
}
obj* l_lean_ir_parse__defconst(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_5 = l_lean_ir_parse__defconst___closed__1;
x_6 = l_lean_ir_keyword(x_5, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; uint8 x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_6, 1);
x_9 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = 1;
x_13 = l_lean_ir_parse__header(x_12, x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 2);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_14);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_16);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 2);
lean::inc(x_30);
lean::dec(x_25);
x_1 = x_26;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_25, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 x_36 = x_25;
} else {
 lean::inc(x_33);
 lean::dec(x_25);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_11);
x_40 = lean::cnstr_get(x_13, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_43 = x_13;
} else {
 lean::inc(x_40);
 lean::dec(x_13);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = x_44;
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_1 = x_47;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_46, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_set(x_46, 0, lean::box(0));
 x_57 = x_46;
} else {
 lean::inc(x_54);
 lean::dec(x_46);
 x_57 = lean::box(0);
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
}
else
{
obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_60 = lean::cnstr_get(x_6, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_63 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
return x_65;
}
lbl_4:
{
obj* x_66; obj* x_67; 
x_66 = l_lean_ir_parse__typed__assignment___closed__3;
x_67 = l_lean_ir_symbol(x_66, x_2);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_68 = lean::cnstr_get(x_67, 1);
x_70 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_set(x_67, 1, lean::box(0));
 lean::cnstr_set(x_67, 2, lean::box(0));
 x_72 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_67);
 x_72 = lean::box(0);
}
x_73 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(x_68);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 2);
lean::inc(x_79);
lean::dec(x_74);
x_82 = lean::apply_1(x_1, x_75);
x_83 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_72)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_72;
}
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_77);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_85);
return x_86;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_1);
lean::dec(x_72);
x_89 = lean::cnstr_get(x_74, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_set(x_74, 0, lean::box(0));
 x_92 = x_74;
} else {
 lean::inc(x_89);
 lean::dec(x_74);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_94);
return x_95;
}
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_1);
x_97 = lean::cnstr_get(x_67, 0);
x_99 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_set(x_67, 0, lean::box(0));
 x_100 = x_67;
} else {
 lean::inc(x_97);
 lean::dec(x_67);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_102);
return x_103;
}
}
}
}
obj* _init_l_lean_ir_parse__external___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("external");
return x_0;
}
}
obj* l_lean_ir_parse__external(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_ir_parse__external___closed__1;
x_2 = l_lean_ir_keyword(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = 0;
x_9 = l_lean_ir_parse__header(x_8, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_7)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_7;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_20);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_7);
x_23 = lean::cnstr_get(x_9, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_26 = x_9;
} else {
 lean::inc(x_23);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_28);
return x_29;
}
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_30 = lean::cnstr_get(x_2, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_33 = x_2;
} else {
 lean::inc(x_30);
 lean::dec(x_2);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
return x_35;
}
}
}
obj* l_lean_ir_parse__decl(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_ir_parse__def(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
lean::inc(x_0);
x_9 = l_lean_ir_parse__defconst(x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_4, x_9);
return x_11;
}
else
{
obj* x_12; uint8 x_14; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_14 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_9);
x_16 = l_lean_ir_parse__external(x_0);
x_17 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_12, x_16);
x_18 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_4, x_17);
return x_18;
}
else
{
obj* x_21; 
lean::dec(x_0);
lean::dec(x_12);
x_21 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_4, x_9);
return x_21;
}
}
}
else
{
lean::dec(x_4);
lean::dec(x_0);
return x_2;
}
}
}
}
void initialize_init_lean_ir_ir();
void initialize_init_lean_parser_parsec();
void initialize_init_lean_parser_identifier();
void initialize_init_lean_parser_string__literal();
void initialize_init_lean_ir_reserved();
static bool _G_initialized = false;
void initialize_init_lean_ir_parser() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_ir();
 initialize_init_lean_parser_parsec();
 initialize_init_lean_parser_identifier();
 initialize_init_lean_parser_string__literal();
 initialize_init_lean_ir_reserved();
 l_lean_ir_keyword___closed__1 = _init_l_lean_ir_keyword___closed__1();
lean::mark_persistent(l_lean_ir_keyword___closed__1);
 l_lean_ir_str2type = _init_l_lean_ir_str2type();
lean::mark_persistent(l_lean_ir_str2type);
 l_lean_ir_str2aunop = _init_l_lean_ir_str2aunop();
lean::mark_persistent(l_lean_ir_str2aunop);
 l_lean_ir_str2abinop = _init_l_lean_ir_str2abinop();
lean::mark_persistent(l_lean_ir_str2abinop);
 l_lean_ir_str2unop = _init_l_lean_ir_str2unop();
lean::mark_persistent(l_lean_ir_str2unop);
 l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1 = _init_l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1();
lean::mark_persistent(l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1);
 l_lean_ir_parse__literal___closed__1 = _init_l_lean_ir_parse__literal___closed__1();
lean::mark_persistent(l_lean_ir_parse__literal___closed__1);
 l_lean_ir_parse__literal___closed__2 = _init_l_lean_ir_parse__literal___closed__2();
lean::mark_persistent(l_lean_ir_parse__literal___closed__2);
 l_lean_ir_parse__literal___closed__3 = _init_l_lean_ir_parse__literal___closed__3();
lean::mark_persistent(l_lean_ir_parse__literal___closed__3);
 l_lean_ir_parse__uint16___closed__1 = _init_l_lean_ir_parse__uint16___closed__1();
lean::mark_persistent(l_lean_ir_parse__uint16___closed__1);
 l_lean_ir_parse__uint16___closed__2 = _init_l_lean_ir_parse__uint16___closed__2();
lean::mark_persistent(l_lean_ir_parse__uint16___closed__2);
 l_lean_ir_parse__usize___closed__1 = _init_l_lean_ir_parse__usize___closed__1();
lean::mark_persistent(l_lean_ir_parse__usize___closed__1);
 l_lean_ir_parse__usize___closed__2 = _init_l_lean_ir_parse__usize___closed__2();
lean::mark_persistent(l_lean_ir_parse__usize___closed__2);
 l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1 = _init_l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1();
lean::mark_persistent(l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1);
 l_lean_ir_identifier___closed__1 = _init_l_lean_ir_identifier___closed__1();
lean::mark_persistent(l_lean_ir_identifier___closed__1);
 l_lean_ir_parse__var___closed__1 = _init_l_lean_ir_parse__var___closed__1();
lean::mark_persistent(l_lean_ir_parse__var___closed__1);
 l_lean_ir_parse__fnid___closed__1 = _init_l_lean_ir_parse__fnid___closed__1();
lean::mark_persistent(l_lean_ir_parse__fnid___closed__1);
 l_lean_ir_parse__blockid___closed__1 = _init_l_lean_ir_parse__blockid___closed__1();
lean::mark_persistent(l_lean_ir_parse__blockid___closed__1);
 l_lean_ir_parse__typed__assignment___closed__1 = _init_l_lean_ir_parse__typed__assignment___closed__1();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__1);
 l_lean_ir_parse__typed__assignment___closed__2 = _init_l_lean_ir_parse__typed__assignment___closed__2();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__2);
 l_lean_ir_parse__typed__assignment___closed__3 = _init_l_lean_ir_parse__typed__assignment___closed__3();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__3);
 l_lean_ir_parse__typed__assignment___closed__4 = _init_l_lean_ir_parse__typed__assignment___closed__4();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__4);
 l_lean_ir_parse__typed__assignment___closed__5 = _init_l_lean_ir_parse__typed__assignment___closed__5();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__5);
 l_lean_ir_parse__typed__assignment___closed__6 = _init_l_lean_ir_parse__typed__assignment___closed__6();
lean::mark_persistent(l_lean_ir_parse__typed__assignment___closed__6);
 l_lean_ir_parse__untyped__assignment___closed__1 = _init_l_lean_ir_parse__untyped__assignment___closed__1();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__1);
 l_lean_ir_parse__untyped__assignment___closed__2 = _init_l_lean_ir_parse__untyped__assignment___closed__2();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__2);
 l_lean_ir_parse__untyped__assignment___closed__3 = _init_l_lean_ir_parse__untyped__assignment___closed__3();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__3);
 l_lean_ir_parse__untyped__assignment___closed__4 = _init_l_lean_ir_parse__untyped__assignment___closed__4();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__4);
 l_lean_ir_parse__untyped__assignment___closed__5 = _init_l_lean_ir_parse__untyped__assignment___closed__5();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__5);
 l_lean_ir_parse__untyped__assignment___closed__6 = _init_l_lean_ir_parse__untyped__assignment___closed__6();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__6);
 l_lean_ir_parse__untyped__assignment___closed__7 = _init_l_lean_ir_parse__untyped__assignment___closed__7();
lean::mark_persistent(l_lean_ir_parse__untyped__assignment___closed__7);
 l_lean_ir_parse__instr___closed__1 = _init_l_lean_ir_parse__instr___closed__1();
lean::mark_persistent(l_lean_ir_parse__instr___closed__1);
 l_lean_ir_parse__instr___closed__2 = _init_l_lean_ir_parse__instr___closed__2();
lean::mark_persistent(l_lean_ir_parse__instr___closed__2);
 l_lean_ir_parse__instr___closed__3 = _init_l_lean_ir_parse__instr___closed__3();
lean::mark_persistent(l_lean_ir_parse__instr___closed__3);
 l_lean_ir_parse__phi___closed__1 = _init_l_lean_ir_parse__phi___closed__1();
lean::mark_persistent(l_lean_ir_parse__phi___closed__1);
 l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1 = _init_l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1);
 l_lean_ir_parse__terminator___closed__1 = _init_l_lean_ir_parse__terminator___closed__1();
lean::mark_persistent(l_lean_ir_parse__terminator___closed__1);
 l_lean_ir_parse__terminator___closed__2 = _init_l_lean_ir_parse__terminator___closed__2();
lean::mark_persistent(l_lean_ir_parse__terminator___closed__2);
 l_lean_ir_parse__terminator___closed__3 = _init_l_lean_ir_parse__terminator___closed__3();
lean::mark_persistent(l_lean_ir_parse__terminator___closed__3);
 l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1 = _init_l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1);
 l_lean_ir_parse__def___closed__1 = _init_l_lean_ir_parse__def___closed__1();
lean::mark_persistent(l_lean_ir_parse__def___closed__1);
 l_lean_ir_parse__defconst___closed__1 = _init_l_lean_ir_parse__defconst___closed__1();
lean::mark_persistent(l_lean_ir_parse__defconst___closed__1);
 l_lean_ir_parse__external___closed__1 = _init_l_lean_ir_parse__external___closed__1();
lean::mark_persistent(l_lean_ir_parse__external___closed__1);
}
