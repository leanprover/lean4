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
obj* x_30; obj* x_31; obj* x_33; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_30 = x_2;
} else {
 lean::dec(x_2);
 x_30 = lean::box(0);
}
x_31 = l_bool_has__repr___closed__1;
lean::inc(x_0);
x_33 = l_lean_ir_keyword(x_31, x_0);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_30);
x_35 = lean::cnstr_get(x_33, 1);
x_37 = lean::cnstr_get(x_33, 2);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_39 = x_33;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_33);
 x_39 = lean::box(0);
}
x_40 = l_lean_ir_parse__literal___closed__2;
x_41 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_39;
}
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_35);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_45; 
lean::dec(x_0);
x_45 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_43);
return x_45;
}
else
{
obj* x_46; uint8 x_48; 
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
x_26 = x_43;
x_27 = x_46;
x_28 = x_48;
goto lbl_29;
}
}
else
{
obj* x_49; uint8 x_51; obj* x_54; obj* x_55; 
x_49 = lean::cnstr_get(x_33, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
lean::dec(x_33);
lean::inc(x_49);
if (lean::is_scalar(x_30)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_30;
}
lean::cnstr_set(x_54, 0, x_49);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_51);
x_55 = x_54;
x_26 = x_55;
x_27 = x_49;
x_28 = x_51;
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
obj* x_58; obj* x_59; uint8 x_60; 
if (x_28 == 0)
{
obj* x_64; 
lean::dec(x_26);
lean::inc(x_0);
x_64 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_0);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_72; 
x_65 = lean::cnstr_get(x_64, 0);
x_67 = lean::cnstr_get(x_64, 1);
x_69 = lean::cnstr_get(x_64, 2);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_set(x_64, 0, lean::box(0));
 lean::cnstr_set(x_64, 1, lean::box(0));
 lean::cnstr_set(x_64, 2, lean::box(0));
 x_71 = x_64;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::dec(x_64);
 x_71 = lean::box(0);
}
x_72 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_67);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_73 = lean::cnstr_get(x_72, 1);
x_75 = lean::cnstr_get(x_72, 2);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_set(x_72, 1, lean::box(0));
 lean::cnstr_set(x_72, 2, lean::box(0));
 x_77 = x_72;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_72);
 x_77 = lean::box(0);
}
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_71)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_71;
}
lean::cnstr_set(x_79, 0, x_65);
lean::cnstr_set(x_79, 1, x_73);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_80);
x_82 = l_lean_ir_parse__literal___closed__1;
x_83 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_81, x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 2);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::nat2int(x_84);
x_92 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
if (lean::is_scalar(x_77)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_77;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_86);
lean::cnstr_set(x_93, 2, x_78);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_96; obj* x_97; 
lean::dec(x_0);
x_96 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_94);
x_97 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_96);
return x_97;
}
else
{
obj* x_98; uint8 x_100; 
x_98 = lean::cnstr_get(x_94, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
x_58 = x_94;
x_59 = x_98;
x_60 = x_100;
goto lbl_61;
}
}
else
{
obj* x_102; uint8 x_104; obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_77);
x_102 = lean::cnstr_get(x_83, 0);
x_104 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 x_105 = x_83;
} else {
 lean::inc(x_102);
 lean::dec(x_83);
 x_105 = lean::box(0);
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
x_58 = x_108;
x_59 = x_102;
x_60 = x_104;
goto lbl_61;
}
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_65);
x_110 = lean::cnstr_get(x_72, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
if (lean::is_exclusive(x_72)) {
 x_113 = x_72;
} else {
 lean::inc(x_110);
 lean::dec(x_72);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_110);
lean::cnstr_set_scalar(x_114, sizeof(void*)*1, x_112);
x_115 = x_114;
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_115);
x_117 = l_lean_ir_parse__literal___closed__1;
x_118 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_116, x_117);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_118, 2);
lean::inc(x_123);
lean::dec(x_118);
x_126 = lean::nat2int(x_119);
x_127 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_127, 0, x_126);
x_128 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_71)) {
 x_129 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_129 = x_71;
}
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_121);
lean::cnstr_set(x_129, 2, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_129);
if (lean::obj_tag(x_130) == 0)
{
obj* x_132; obj* x_133; 
lean::dec(x_0);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_130);
x_133 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_132);
return x_133;
}
else
{
obj* x_134; uint8 x_136; 
x_134 = lean::cnstr_get(x_130, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get_scalar<uint8>(x_130, sizeof(void*)*1);
x_58 = x_130;
x_59 = x_134;
x_60 = x_136;
goto lbl_61;
}
}
else
{
obj* x_138; uint8 x_140; obj* x_141; obj* x_143; obj* x_144; 
lean::dec(x_71);
x_138 = lean::cnstr_get(x_118, 0);
x_140 = lean::cnstr_get_scalar<uint8>(x_118, sizeof(void*)*1);
if (lean::is_exclusive(x_118)) {
 x_141 = x_118;
} else {
 lean::inc(x_138);
 lean::dec(x_118);
 x_141 = lean::box(0);
}
lean::inc(x_138);
if (lean::is_scalar(x_141)) {
 x_143 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_143 = x_141;
}
lean::cnstr_set(x_143, 0, x_138);
lean::cnstr_set_scalar(x_143, sizeof(void*)*1, x_140);
x_144 = x_143;
x_58 = x_144;
x_59 = x_138;
x_60 = x_140;
goto lbl_61;
}
}
}
else
{
obj* x_145; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_145 = lean::cnstr_get(x_64, 0);
x_147 = lean::cnstr_get_scalar<uint8>(x_64, sizeof(void*)*1);
if (lean::is_exclusive(x_64)) {
 x_148 = x_64;
} else {
 lean::inc(x_145);
 lean::dec(x_64);
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
x_151 = l_lean_ir_parse__literal___closed__1;
x_152 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_150, x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_153 = lean::cnstr_get(x_152, 0);
x_155 = lean::cnstr_get(x_152, 1);
x_157 = lean::cnstr_get(x_152, 2);
if (lean::is_exclusive(x_152)) {
 x_159 = x_152;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::inc(x_157);
 lean::dec(x_152);
 x_159 = lean::box(0);
}
x_160 = lean::nat2int(x_153);
x_161 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_161, 0, x_160);
x_162 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_159)) {
 x_163 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_163 = x_159;
}
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_155);
lean::cnstr_set(x_163, 2, x_162);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_157, x_163);
if (lean::obj_tag(x_164) == 0)
{
obj* x_166; obj* x_167; 
lean::dec(x_0);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_164);
x_167 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_166);
return x_167;
}
else
{
obj* x_168; uint8 x_170; 
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get_scalar<uint8>(x_164, sizeof(void*)*1);
x_58 = x_164;
x_59 = x_168;
x_60 = x_170;
goto lbl_61;
}
}
else
{
obj* x_171; uint8 x_173; obj* x_174; obj* x_176; obj* x_177; 
x_171 = lean::cnstr_get(x_152, 0);
x_173 = lean::cnstr_get_scalar<uint8>(x_152, sizeof(void*)*1);
if (lean::is_exclusive(x_152)) {
 x_174 = x_152;
} else {
 lean::inc(x_171);
 lean::dec(x_152);
 x_174 = lean::box(0);
}
lean::inc(x_171);
if (lean::is_scalar(x_174)) {
 x_176 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_176 = x_174;
}
lean::cnstr_set(x_176, 0, x_171);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_173);
x_177 = x_176;
x_58 = x_177;
x_59 = x_171;
x_60 = x_173;
goto lbl_61;
}
}
}
else
{
obj* x_180; 
lean::dec(x_0);
lean::dec(x_27);
x_180 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_26);
return x_180;
}
lbl_61:
{
obj* x_181; obj* x_182; obj* x_183; obj* x_185; uint8 x_186; 
if (x_60 == 0)
{
obj* x_190; 
lean::dec(x_58);
lean::inc(x_0);
x_190 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_1, x_0);
if (lean::obj_tag(x_190) == 0)
{
obj* x_191; obj* x_193; obj* x_195; obj* x_196; 
x_191 = lean::cnstr_get(x_190, 1);
x_193 = lean::cnstr_get(x_190, 2);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_set(x_190, 1, lean::box(0));
 lean::cnstr_set(x_190, 2, lean::box(0));
 x_195 = x_190;
} else {
 lean::inc(x_191);
 lean::inc(x_193);
 lean::dec(x_190);
 x_195 = lean::box(0);
}
x_196 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_191);
if (lean::obj_tag(x_196) == 0)
{
obj* x_197; obj* x_199; obj* x_201; obj* x_204; 
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_196, 2);
lean::inc(x_201);
lean::dec(x_196);
x_204 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_199);
if (lean::obj_tag(x_204) == 0)
{
obj* x_205; obj* x_207; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
x_205 = lean::cnstr_get(x_204, 1);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_204, 2);
lean::inc(x_207);
lean::dec(x_204);
x_210 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_195)) {
 x_211 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_211 = x_195;
}
lean::cnstr_set(x_211, 0, x_197);
lean::cnstr_set(x_211, 1, x_205);
lean::cnstr_set(x_211, 2, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_207, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_201, x_212);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_213);
if (lean::obj_tag(x_214) == 0)
{
obj* x_215; obj* x_217; obj* x_219; 
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_214, 2);
lean::inc(x_219);
lean::dec(x_214);
x_181 = x_215;
x_182 = x_217;
x_183 = x_219;
goto lbl_184;
}
else
{
obj* x_222; uint8 x_224; 
x_222 = lean::cnstr_get(x_214, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get_scalar<uint8>(x_214, sizeof(void*)*1);
lean::dec(x_214);
x_185 = x_222;
x_186 = x_224;
goto lbl_187;
}
}
else
{
obj* x_228; uint8 x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_197);
lean::dec(x_195);
x_228 = lean::cnstr_get(x_204, 0);
x_230 = lean::cnstr_get_scalar<uint8>(x_204, sizeof(void*)*1);
if (lean::is_exclusive(x_204)) {
 x_231 = x_204;
} else {
 lean::inc(x_228);
 lean::dec(x_204);
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
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_201, x_233);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_234);
if (lean::obj_tag(x_235) == 0)
{
obj* x_236; obj* x_238; obj* x_240; 
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_235, 2);
lean::inc(x_240);
lean::dec(x_235);
x_181 = x_236;
x_182 = x_238;
x_183 = x_240;
goto lbl_184;
}
else
{
obj* x_243; uint8 x_245; 
x_243 = lean::cnstr_get(x_235, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get_scalar<uint8>(x_235, sizeof(void*)*1);
lean::dec(x_235);
x_185 = x_243;
x_186 = x_245;
goto lbl_187;
}
}
}
else
{
obj* x_248; uint8 x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_195);
x_248 = lean::cnstr_get(x_196, 0);
x_250 = lean::cnstr_get_scalar<uint8>(x_196, sizeof(void*)*1);
if (lean::is_exclusive(x_196)) {
 x_251 = x_196;
} else {
 lean::inc(x_248);
 lean::dec(x_196);
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
x_254 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_253);
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
x_181 = x_255;
x_182 = x_257;
x_183 = x_259;
goto lbl_184;
}
else
{
obj* x_262; uint8 x_264; 
x_262 = lean::cnstr_get(x_254, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get_scalar<uint8>(x_254, sizeof(void*)*1);
lean::dec(x_254);
x_185 = x_262;
x_186 = x_264;
goto lbl_187;
}
}
}
else
{
obj* x_266; uint8 x_268; 
x_266 = lean::cnstr_get(x_190, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*1);
lean::dec(x_190);
x_185 = x_266;
x_186 = x_268;
goto lbl_187;
}
}
else
{
obj* x_272; obj* x_273; 
lean::dec(x_0);
lean::dec(x_59);
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_58);
x_273 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_272);
return x_273;
}
lbl_184:
{
obj* x_274; obj* x_275; obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
x_274 = lean::nat2int(x_181);
x_275 = lean::int_neg(x_274);
lean::dec(x_274);
x_277 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_277, 0, x_275);
x_278 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_279 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_279, 0, x_277);
lean::cnstr_set(x_279, 1, x_182);
lean::cnstr_set(x_279, 2, x_278);
x_280 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_279);
if (lean::obj_tag(x_280) == 0)
{
obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_0);
x_282 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_280);
x_283 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_282);
x_284 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_283);
return x_284;
}
else
{
obj* x_285; uint8 x_287; 
x_285 = lean::cnstr_get(x_280, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get_scalar<uint8>(x_280, sizeof(void*)*1);
if (x_287 == 0)
{
obj* x_288; obj* x_289; 
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 x_288 = x_280;
} else {
 lean::dec(x_280);
 x_288 = lean::box(0);
}
x_289 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_289) == 0)
{
obj* x_291; obj* x_293; obj* x_295; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; 
lean::dec(x_288);
x_291 = lean::cnstr_get(x_289, 0);
x_293 = lean::cnstr_get(x_289, 1);
x_295 = lean::cnstr_get(x_289, 2);
if (lean::is_exclusive(x_289)) {
 x_297 = x_289;
} else {
 lean::inc(x_291);
 lean::inc(x_293);
 lean::inc(x_295);
 lean::dec(x_289);
 x_297 = lean::box(0);
}
x_298 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_298, 0, x_291);
if (lean::is_scalar(x_297)) {
 x_299 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_299 = x_297;
}
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_293);
lean::cnstr_set(x_299, 2, x_278);
x_300 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_295, x_299);
x_301 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_285, x_300);
x_302 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_301);
x_303 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_302);
x_304 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_303);
return x_304;
}
else
{
obj* x_305; uint8 x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_289, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get_scalar<uint8>(x_289, sizeof(void*)*1);
lean::dec(x_289);
if (lean::is_scalar(x_288)) {
 x_309 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_309 = x_288;
}
lean::cnstr_set(x_309, 0, x_305);
lean::cnstr_set_scalar(x_309, sizeof(void*)*1, x_307);
x_310 = x_309;
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_285, x_310);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_311);
x_313 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_312);
x_314 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_313);
return x_314;
}
}
else
{
obj* x_317; obj* x_318; obj* x_319; 
lean::dec(x_0);
lean::dec(x_285);
x_317 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_280);
x_318 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_317);
x_319 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_318);
return x_319;
}
}
}
lbl_187:
{
if (x_186 == 0)
{
obj* x_320; 
x_320 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_320) == 0)
{
obj* x_321; obj* x_323; obj* x_325; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_321 = lean::cnstr_get(x_320, 0);
x_323 = lean::cnstr_get(x_320, 1);
x_325 = lean::cnstr_get(x_320, 2);
if (lean::is_exclusive(x_320)) {
 x_327 = x_320;
} else {
 lean::inc(x_321);
 lean::inc(x_323);
 lean::inc(x_325);
 lean::dec(x_320);
 x_327 = lean::box(0);
}
x_328 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_328, 0, x_321);
x_329 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_327)) {
 x_330 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_330 = x_327;
}
lean::cnstr_set(x_330, 0, x_328);
lean::cnstr_set(x_330, 1, x_323);
lean::cnstr_set(x_330, 2, x_329);
x_331 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_325, x_330);
x_332 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_185, x_331);
x_333 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_332);
x_334 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_333);
x_335 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_334);
return x_335;
}
else
{
obj* x_336; uint8 x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
x_336 = lean::cnstr_get(x_320, 0);
x_338 = lean::cnstr_get_scalar<uint8>(x_320, sizeof(void*)*1);
if (lean::is_exclusive(x_320)) {
 x_339 = x_320;
} else {
 lean::inc(x_336);
 lean::dec(x_320);
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
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_185, x_341);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_343);
x_345 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_344);
return x_345;
}
}
else
{
obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
lean::dec(x_0);
x_347 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_347, 0, x_185);
lean::cnstr_set_scalar(x_347, sizeof(void*)*1, x_186);
x_348 = x_347;
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_59, x_348);
x_350 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_349);
x_351 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_350);
return x_351;
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
obj* x_111; obj* x_113; 
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_111 = x_26;
} else {
 lean::dec(x_26);
 x_111 = lean::box(0);
}
lean::inc(x_21);
x_113 = l_lean_ir_parse__var(x_21);
if (lean::obj_tag(x_113) == 0)
{
obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; uint8 x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_111);
x_115 = lean::cnstr_get(x_113, 0);
x_117 = lean::cnstr_get(x_113, 1);
x_119 = lean::cnstr_get(x_113, 2);
if (lean::is_exclusive(x_113)) {
 x_121 = x_113;
} else {
 lean::inc(x_115);
 lean::inc(x_117);
 lean::inc(x_119);
 lean::dec(x_113);
 x_121 = lean::box(0);
}
lean::inc(x_0);
x_123 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_123, 0, x_0);
lean::cnstr_set(x_123, 1, x_115);
x_124 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_123, sizeof(void*)*2, x_124);
x_125 = x_123;
x_126 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_121)) {
 x_127 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_127 = x_121;
}
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_117);
lean::cnstr_set(x_127, 2, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_134 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_128);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_136);
return x_137;
}
else
{
obj* x_138; uint8 x_140; 
x_138 = lean::cnstr_get(x_128, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get_scalar<uint8>(x_128, sizeof(void*)*1);
x_107 = x_128;
x_108 = x_138;
x_109 = x_140;
goto lbl_110;
}
}
else
{
obj* x_141; uint8 x_143; obj* x_146; obj* x_147; 
x_141 = lean::cnstr_get(x_113, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
lean::dec(x_113);
lean::inc(x_141);
if (lean::is_scalar(x_111)) {
 x_146 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_146 = x_111;
}
lean::cnstr_set(x_146, 0, x_141);
lean::cnstr_set_scalar(x_146, sizeof(void*)*1, x_143);
x_147 = x_146;
x_107 = x_147;
x_108 = x_141;
x_109 = x_143;
goto lbl_110;
}
}
else
{
obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
lean::dec(x_104);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_156);
return x_157;
}
lbl_110:
{
obj* x_158; obj* x_159; uint8 x_160; 
if (x_109 == 0)
{
obj* x_163; obj* x_164; obj* x_166; 
lean::dec(x_107);
x_163 = l_lean_ir_parse__typed__assignment___closed__5;
x_164 = l_lean_ir_str2aunop;
lean::inc(x_21);
x_166 = l_lean_ir_parse__key2val___main___rarg(x_163, x_164, x_21);
if (lean::obj_tag(x_166) == 0)
{
obj* x_167; obj* x_169; obj* x_171; obj* x_173; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_167 = lean::cnstr_get(x_166, 0);
x_169 = lean::cnstr_get(x_166, 1);
x_171 = lean::cnstr_get(x_166, 2);
if (lean::is_exclusive(x_166)) {
 x_173 = x_166;
} else {
 lean::inc(x_167);
 lean::inc(x_169);
 lean::inc(x_171);
 lean::dec(x_166);
 x_173 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_176 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__2___boxed), 4, 3);
lean::closure_set(x_176, 0, x_0);
lean::closure_set(x_176, 1, x_12);
lean::closure_set(x_176, 2, x_167);
x_177 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_173)) {
 x_178 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_178 = x_173;
}
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_169);
lean::cnstr_set(x_178, 2, x_177);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_178);
if (lean::obj_tag(x_179) == 0)
{
obj* x_180; obj* x_182; obj* x_184; obj* x_186; obj* x_187; 
x_180 = lean::cnstr_get(x_179, 0);
x_182 = lean::cnstr_get(x_179, 1);
x_184 = lean::cnstr_get(x_179, 2);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_set(x_179, 0, lean::box(0));
 lean::cnstr_set(x_179, 1, lean::box(0));
 lean::cnstr_set(x_179, 2, lean::box(0));
 x_186 = x_179;
} else {
 lean::inc(x_180);
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_179);
 x_186 = lean::box(0);
}
x_187 = l_lean_ir_parse__var(x_182);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_190; obj* x_192; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_187, 2);
lean::inc(x_192);
lean::dec(x_187);
x_195 = lean::apply_1(x_180, x_188);
if (lean::is_scalar(x_186)) {
 x_196 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_196 = x_186;
}
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_190);
lean::cnstr_set(x_196, 2, x_177);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_196);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_184, x_197);
if (lean::obj_tag(x_198) == 0)
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_198);
x_206 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_205);
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_206);
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_207);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_208);
return x_209;
}
else
{
obj* x_210; uint8 x_212; 
x_210 = lean::cnstr_get(x_198, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get_scalar<uint8>(x_198, sizeof(void*)*1);
x_158 = x_198;
x_159 = x_210;
x_160 = x_212;
goto lbl_161;
}
}
else
{
obj* x_215; uint8 x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_186);
lean::dec(x_180);
x_215 = lean::cnstr_get(x_187, 0);
x_217 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*1);
if (lean::is_exclusive(x_187)) {
 x_218 = x_187;
} else {
 lean::inc(x_215);
 lean::dec(x_187);
 x_218 = lean::box(0);
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_215);
lean::cnstr_set_scalar(x_219, sizeof(void*)*1, x_217);
x_220 = x_219;
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_184, x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_221);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_228);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_230);
x_232 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_231);
return x_232;
}
else
{
obj* x_233; uint8 x_235; 
x_233 = lean::cnstr_get(x_221, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
x_158 = x_221;
x_159 = x_233;
x_160 = x_235;
goto lbl_161;
}
}
}
else
{
obj* x_236; uint8 x_238; obj* x_239; obj* x_241; obj* x_242; 
x_236 = lean::cnstr_get(x_179, 0);
x_238 = lean::cnstr_get_scalar<uint8>(x_179, sizeof(void*)*1);
if (lean::is_exclusive(x_179)) {
 x_239 = x_179;
} else {
 lean::inc(x_236);
 lean::dec(x_179);
 x_239 = lean::box(0);
}
lean::inc(x_236);
if (lean::is_scalar(x_239)) {
 x_241 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_241 = x_239;
}
lean::cnstr_set(x_241, 0, x_236);
lean::cnstr_set_scalar(x_241, sizeof(void*)*1, x_238);
x_242 = x_241;
x_158 = x_242;
x_159 = x_236;
x_160 = x_238;
goto lbl_161;
}
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_248; obj* x_249; 
x_243 = lean::cnstr_get(x_166, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_166, sizeof(void*)*1);
if (lean::is_exclusive(x_166)) {
 x_246 = x_166;
} else {
 lean::inc(x_243);
 lean::dec(x_166);
 x_246 = lean::box(0);
}
lean::inc(x_243);
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_243);
lean::cnstr_set_scalar(x_248, sizeof(void*)*1, x_245);
x_249 = x_248;
x_158 = x_249;
x_159 = x_243;
x_160 = x_245;
goto lbl_161;
}
}
else
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_108);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_107);
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_257);
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_258);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_259);
return x_260;
}
lbl_161:
{
obj* x_261; obj* x_262; uint8 x_263; obj* x_265; obj* x_266; obj* x_267; 
if (x_160 == 0)
{
obj* x_270; obj* x_271; obj* x_273; 
lean::dec(x_158);
x_270 = l_lean_ir_parse__typed__assignment___closed__4;
x_271 = l_lean_ir_str2abinop;
lean::inc(x_21);
x_273 = l_lean_ir_parse__key2val___main___rarg(x_270, x_271, x_21);
if (lean::obj_tag(x_273) == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_280; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_274 = lean::cnstr_get(x_273, 0);
x_276 = lean::cnstr_get(x_273, 1);
x_278 = lean::cnstr_get(x_273, 2);
if (lean::is_exclusive(x_273)) {
 lean::cnstr_set(x_273, 0, lean::box(0));
 lean::cnstr_set(x_273, 1, lean::box(0));
 lean::cnstr_set(x_273, 2, lean::box(0));
 x_280 = x_273;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::inc(x_278);
 lean::dec(x_273);
 x_280 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_283 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__1___boxed), 5, 3);
lean::closure_set(x_283, 0, x_0);
lean::closure_set(x_283, 1, x_12);
lean::closure_set(x_283, 2, x_274);
x_284 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_285 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_285 = x_25;
}
lean::cnstr_set(x_285, 0, x_283);
lean::cnstr_set(x_285, 1, x_276);
lean::cnstr_set(x_285, 2, x_284);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_278, x_285);
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
x_294 = l_lean_ir_parse__var(x_289);
if (lean::obj_tag(x_294) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_302; obj* x_303; obj* x_304; obj* x_305; 
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_294, 2);
lean::inc(x_299);
lean::dec(x_294);
x_302 = lean::apply_1(x_287, x_295);
if (lean::is_scalar(x_280)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_280;
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_297);
lean::cnstr_set(x_303, 2, x_284);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_299, x_303);
x_305 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_304);
if (lean::obj_tag(x_305) == 0)
{
obj* x_306; obj* x_308; obj* x_310; 
x_306 = lean::cnstr_get(x_305, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get(x_305, 1);
lean::inc(x_308);
x_310 = lean::cnstr_get(x_305, 2);
lean::inc(x_310);
lean::dec(x_305);
x_265 = x_306;
x_266 = x_308;
x_267 = x_310;
goto lbl_268;
}
else
{
obj* x_314; uint8 x_316; obj* x_317; obj* x_319; obj* x_320; 
lean::dec(x_18);
x_314 = lean::cnstr_get(x_305, 0);
x_316 = lean::cnstr_get_scalar<uint8>(x_305, sizeof(void*)*1);
if (lean::is_exclusive(x_305)) {
 x_317 = x_305;
} else {
 lean::inc(x_314);
 lean::dec(x_305);
 x_317 = lean::box(0);
}
lean::inc(x_314);
if (lean::is_scalar(x_317)) {
 x_319 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_319 = x_317;
}
lean::cnstr_set(x_319, 0, x_314);
lean::cnstr_set_scalar(x_319, sizeof(void*)*1, x_316);
x_320 = x_319;
x_261 = x_320;
x_262 = x_314;
x_263 = x_316;
goto lbl_264;
}
}
else
{
obj* x_323; uint8 x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_287);
lean::dec(x_280);
x_323 = lean::cnstr_get(x_294, 0);
x_325 = lean::cnstr_get_scalar<uint8>(x_294, sizeof(void*)*1);
if (lean::is_exclusive(x_294)) {
 x_326 = x_294;
} else {
 lean::inc(x_323);
 lean::dec(x_294);
 x_326 = lean::box(0);
}
if (lean::is_scalar(x_326)) {
 x_327 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_327 = x_326;
}
lean::cnstr_set(x_327, 0, x_323);
lean::cnstr_set_scalar(x_327, sizeof(void*)*1, x_325);
x_328 = x_327;
x_329 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_328);
if (lean::obj_tag(x_329) == 0)
{
obj* x_330; obj* x_332; obj* x_334; 
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_329, 2);
lean::inc(x_334);
lean::dec(x_329);
x_265 = x_330;
x_266 = x_332;
x_267 = x_334;
goto lbl_268;
}
else
{
obj* x_338; uint8 x_340; obj* x_341; obj* x_343; obj* x_344; 
lean::dec(x_18);
x_338 = lean::cnstr_get(x_329, 0);
x_340 = lean::cnstr_get_scalar<uint8>(x_329, sizeof(void*)*1);
if (lean::is_exclusive(x_329)) {
 x_341 = x_329;
} else {
 lean::inc(x_338);
 lean::dec(x_329);
 x_341 = lean::box(0);
}
lean::inc(x_338);
if (lean::is_scalar(x_341)) {
 x_343 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_343 = x_341;
}
lean::cnstr_set(x_343, 0, x_338);
lean::cnstr_set_scalar(x_343, sizeof(void*)*1, x_340);
x_344 = x_343;
x_261 = x_344;
x_262 = x_338;
x_263 = x_340;
goto lbl_264;
}
}
}
else
{
obj* x_347; uint8 x_349; obj* x_350; obj* x_352; obj* x_353; 
lean::dec(x_18);
lean::dec(x_280);
x_347 = lean::cnstr_get(x_286, 0);
x_349 = lean::cnstr_get_scalar<uint8>(x_286, sizeof(void*)*1);
if (lean::is_exclusive(x_286)) {
 x_350 = x_286;
} else {
 lean::inc(x_347);
 lean::dec(x_286);
 x_350 = lean::box(0);
}
lean::inc(x_347);
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_347);
lean::cnstr_set_scalar(x_352, sizeof(void*)*1, x_349);
x_353 = x_352;
x_261 = x_353;
x_262 = x_347;
x_263 = x_349;
goto lbl_264;
}
}
else
{
obj* x_356; uint8 x_358; obj* x_359; obj* x_361; obj* x_362; 
lean::dec(x_18);
lean::dec(x_25);
x_356 = lean::cnstr_get(x_273, 0);
x_358 = lean::cnstr_get_scalar<uint8>(x_273, sizeof(void*)*1);
if (lean::is_exclusive(x_273)) {
 x_359 = x_273;
} else {
 lean::inc(x_356);
 lean::dec(x_273);
 x_359 = lean::box(0);
}
lean::inc(x_356);
if (lean::is_scalar(x_359)) {
 x_361 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_361 = x_359;
}
lean::cnstr_set(x_361, 0, x_356);
lean::cnstr_set_scalar(x_361, sizeof(void*)*1, x_358);
x_362 = x_361;
x_261 = x_362;
x_262 = x_356;
x_263 = x_358;
goto lbl_264;
}
}
else
{
obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_18);
lean::dec(x_25);
lean::dec(x_159);
x_370 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_158);
x_371 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_370);
x_372 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_371);
x_373 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_372);
x_374 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_373);
return x_374;
}
lbl_264:
{
if (x_263 == 0)
{
obj* x_376; 
lean::dec(x_261);
x_376 = l_lean_ir_parse__literal(x_21);
if (lean::obj_tag(x_376) == 0)
{
obj* x_377; obj* x_379; obj* x_381; obj* x_384; uint8 x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; 
x_377 = lean::cnstr_get(x_376, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_376, 1);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_376, 2);
lean::inc(x_381);
lean::dec(x_376);
x_384 = lean::alloc_cnstr(1, 2, 1);
lean::cnstr_set(x_384, 0, x_0);
lean::cnstr_set(x_384, 1, x_377);
x_385 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_384, sizeof(void*)*2, x_385);
x_386 = x_384;
x_387 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_388 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_388 = x_8;
}
lean::cnstr_set(x_388, 0, x_386);
lean::cnstr_set(x_388, 1, x_379);
lean::cnstr_set(x_388, 2, x_387);
x_389 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_381, x_388);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_262, x_389);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_390);
x_392 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_391);
x_393 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_392);
x_394 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_393);
x_395 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_394);
x_396 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_395);
return x_396;
}
else
{
obj* x_400; uint8 x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
x_400 = lean::cnstr_get(x_376, 0);
x_402 = lean::cnstr_get_scalar<uint8>(x_376, sizeof(void*)*1);
if (lean::is_exclusive(x_376)) {
 x_403 = x_376;
} else {
 lean::inc(x_400);
 lean::dec(x_376);
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
x_406 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_262, x_405);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_406);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_407);
x_409 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_408);
x_410 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_409);
x_411 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_410);
x_412 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_411);
return x_412;
}
}
else
{
obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_262);
lean::dec(x_21);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_261);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_418);
x_420 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_419);
x_421 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_420);
x_422 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_421);
x_423 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_422);
return x_423;
}
}
lbl_268:
{
obj* x_424; 
x_424 = l_lean_ir_parse__var(x_266);
if (lean::obj_tag(x_424) == 0)
{
obj* x_425; obj* x_427; obj* x_429; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_436; 
x_425 = lean::cnstr_get(x_424, 0);
lean::inc(x_425);
x_427 = lean::cnstr_get(x_424, 1);
lean::inc(x_427);
x_429 = lean::cnstr_get(x_424, 2);
lean::inc(x_429);
lean::dec(x_424);
x_432 = lean::apply_1(x_265, x_425);
x_433 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_434 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_434 = x_18;
}
lean::cnstr_set(x_434, 0, x_432);
lean::cnstr_set(x_434, 1, x_427);
lean::cnstr_set(x_434, 2, x_433);
x_435 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_429, x_434);
x_436 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_267, x_435);
if (lean::obj_tag(x_436) == 0)
{
obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
x_441 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_436);
x_442 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_441);
x_443 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_442);
x_444 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_443);
x_445 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_444);
x_446 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_445);
return x_446;
}
else
{
obj* x_447; uint8 x_449; 
x_447 = lean::cnstr_get(x_436, 0);
lean::inc(x_447);
x_449 = lean::cnstr_get_scalar<uint8>(x_436, sizeof(void*)*1);
x_261 = x_436;
x_262 = x_447;
x_263 = x_449;
goto lbl_264;
}
}
else
{
obj* x_452; uint8 x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; 
lean::dec(x_265);
lean::dec(x_18);
x_452 = lean::cnstr_get(x_424, 0);
x_454 = lean::cnstr_get_scalar<uint8>(x_424, sizeof(void*)*1);
if (lean::is_exclusive(x_424)) {
 x_455 = x_424;
} else {
 lean::inc(x_452);
 lean::dec(x_424);
 x_455 = lean::box(0);
}
if (lean::is_scalar(x_455)) {
 x_456 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_456 = x_455;
}
lean::cnstr_set(x_456, 0, x_452);
lean::cnstr_set_scalar(x_456, sizeof(void*)*1, x_454);
x_457 = x_456;
x_458 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_267, x_457);
if (lean::obj_tag(x_458) == 0)
{
obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_21);
x_463 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_159, x_458);
x_464 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_463);
x_465 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_464);
x_466 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_465);
x_467 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_466);
x_468 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_467);
return x_468;
}
else
{
obj* x_469; uint8 x_471; 
x_469 = lean::cnstr_get(x_458, 0);
lean::inc(x_469);
x_471 = lean::cnstr_get_scalar<uint8>(x_458, sizeof(void*)*1);
x_261 = x_458;
x_262 = x_469;
x_263 = x_471;
goto lbl_264;
}
}
}
}
}
}
}
lbl_31:
{
obj* x_472; 
x_472 = l_lean_ir_parse__usize(x_29);
if (lean::obj_tag(x_472) == 0)
{
obj* x_473; obj* x_475; obj* x_477; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; 
x_473 = lean::cnstr_get(x_472, 0);
x_475 = lean::cnstr_get(x_472, 1);
x_477 = lean::cnstr_get(x_472, 2);
if (lean::is_exclusive(x_472)) {
 x_479 = x_472;
} else {
 lean::inc(x_473);
 lean::inc(x_475);
 lean::inc(x_477);
 lean::dec(x_472);
 x_479 = lean::box(0);
}
x_480 = lean::apply_1(x_28, x_473);
x_481 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_479)) {
 x_482 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_482 = x_479;
}
lean::cnstr_set(x_482, 0, x_480);
lean::cnstr_set(x_482, 1, x_475);
lean::cnstr_set(x_482, 2, x_481);
x_483 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_482);
x_484 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_483);
x_26 = x_484;
goto lbl_27;
}
else
{
obj* x_486; uint8 x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; 
lean::dec(x_28);
x_486 = lean::cnstr_get(x_472, 0);
x_488 = lean::cnstr_get_scalar<uint8>(x_472, sizeof(void*)*1);
if (lean::is_exclusive(x_472)) {
 x_489 = x_472;
} else {
 lean::inc(x_486);
 lean::dec(x_472);
 x_489 = lean::box(0);
}
if (lean::is_scalar(x_489)) {
 x_490 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_490 = x_489;
}
lean::cnstr_set(x_490, 0, x_486);
lean::cnstr_set_scalar(x_490, sizeof(void*)*1, x_488);
x_491 = x_490;
x_492 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_491);
x_26 = x_492;
goto lbl_27;
}
}
}
else
{
obj* x_497; uint8 x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_18);
x_497 = lean::cnstr_get(x_20, 0);
x_499 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_500 = x_20;
} else {
 lean::inc(x_497);
 lean::dec(x_20);
 x_500 = lean::box(0);
}
if (lean::is_scalar(x_500)) {
 x_501 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_501 = x_500;
}
lean::cnstr_set(x_501, 0, x_497);
lean::cnstr_set_scalar(x_501, sizeof(void*)*1, x_499);
x_502 = x_501;
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_502);
x_504 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_503);
return x_504;
}
}
else
{
obj* x_507; uint8 x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; 
lean::dec(x_8);
lean::dec(x_0);
x_507 = lean::cnstr_get(x_11, 0);
x_509 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_510 = x_11;
} else {
 lean::inc(x_507);
 lean::dec(x_11);
 x_510 = lean::box(0);
}
if (lean::is_scalar(x_510)) {
 x_511 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_511 = x_510;
}
lean::cnstr_set(x_511, 0, x_507);
lean::cnstr_set_scalar(x_511, sizeof(void*)*1, x_509);
x_512 = x_511;
x_513 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_512);
return x_513;
}
}
else
{
obj* x_515; uint8 x_517; obj* x_518; obj* x_519; obj* x_520; 
lean::dec(x_0);
x_515 = lean::cnstr_get(x_3, 0);
x_517 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_518 = x_3;
} else {
 lean::inc(x_515);
 lean::dec(x_3);
 x_518 = lean::box(0);
}
if (lean::is_scalar(x_518)) {
 x_519 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_519 = x_518;
}
lean::cnstr_set(x_519, 0, x_515);
lean::cnstr_set_scalar(x_519, sizeof(void*)*1, x_517);
x_520 = x_519;
return x_520;
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
obj* x_88; obj* x_89; obj* x_91; 
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_88 = x_9;
} else {
 lean::dec(x_9);
 x_88 = lean::box(0);
}
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
obj* x_99; obj* x_101; obj* x_103; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_88);
x_99 = lean::cnstr_get(x_97, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_97, 1);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_97, 2);
lean::inc(x_103);
lean::dec(x_97);
lean::inc(x_0);
x_107 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_107, 0, x_0);
lean::cnstr_set(x_107, 1, x_99);
x_108 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_96)) {
 x_109 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_109 = x_96;
}
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_101);
lean::cnstr_set(x_109, 2, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_115; obj* x_116; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_115 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_111);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_115);
return x_116;
}
else
{
obj* x_117; uint8 x_119; 
x_117 = lean::cnstr_get(x_111, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*1);
x_84 = x_111;
x_85 = x_117;
x_86 = x_119;
goto lbl_87;
}
}
else
{
obj* x_121; uint8 x_123; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_96);
x_121 = lean::cnstr_get(x_97, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
lean::dec(x_97);
if (lean::is_scalar(x_88)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_88;
}
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = x_125;
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_132; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_127);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_131);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_127, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
x_84 = x_127;
x_85 = x_133;
x_86 = x_135;
goto lbl_87;
}
}
}
else
{
obj* x_136; uint8 x_138; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_91, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
lean::dec(x_91);
lean::inc(x_136);
if (lean::is_scalar(x_88)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_88;
}
lean::cnstr_set(x_141, 0, x_136);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_138);
x_142 = x_141;
x_84 = x_142;
x_85 = x_136;
x_86 = x_138;
goto lbl_87;
}
}
else
{
obj* x_147; 
lean::dec(x_81);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_147;
}
lbl_87:
{
obj* x_148; obj* x_149; uint8 x_150; obj* x_152; obj* x_153; obj* x_154; 
if (x_86 == 0)
{
obj* x_157; obj* x_159; 
lean::dec(x_84);
x_157 = l_lean_ir_parse__untyped__assignment___closed__5;
lean::inc(x_4);
x_159 = l_lean_ir_keyword(x_157, x_4);
if (lean::obj_tag(x_159) == 0)
{
obj* x_160; obj* x_162; obj* x_164; obj* x_165; 
x_160 = lean::cnstr_get(x_159, 1);
x_162 = lean::cnstr_get(x_159, 2);
if (lean::is_exclusive(x_159)) {
 lean::cnstr_release(x_159, 0);
 lean::cnstr_set(x_159, 1, lean::box(0));
 lean::cnstr_set(x_159, 2, lean::box(0));
 x_164 = x_159;
} else {
 lean::inc(x_160);
 lean::inc(x_162);
 lean::dec(x_159);
 x_164 = lean::box(0);
}
x_165 = l_lean_ir_parse__var(x_160);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_168; obj* x_170; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_165, 1);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_165, 2);
lean::inc(x_170);
lean::dec(x_165);
lean::inc(x_0);
x_174 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__5___boxed), 3, 2);
lean::closure_set(x_174, 0, x_0);
lean::closure_set(x_174, 1, x_166);
x_175 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_164)) {
 x_176 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_176 = x_164;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_168);
lean::cnstr_set(x_176, 2, x_175);
x_177 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_176);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_162, x_177);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_181; obj* x_183; 
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_178, 2);
lean::inc(x_183);
lean::dec(x_178);
x_152 = x_179;
x_153 = x_181;
x_154 = x_183;
goto lbl_155;
}
else
{
obj* x_186; uint8 x_188; obj* x_189; obj* x_191; obj* x_192; 
x_186 = lean::cnstr_get(x_178, 0);
x_188 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
if (lean::is_exclusive(x_178)) {
 x_189 = x_178;
} else {
 lean::inc(x_186);
 lean::dec(x_178);
 x_189 = lean::box(0);
}
lean::inc(x_186);
if (lean::is_scalar(x_189)) {
 x_191 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_191 = x_189;
}
lean::cnstr_set(x_191, 0, x_186);
lean::cnstr_set_scalar(x_191, sizeof(void*)*1, x_188);
x_192 = x_191;
x_148 = x_192;
x_149 = x_186;
x_150 = x_188;
goto lbl_151;
}
}
else
{
obj* x_194; uint8 x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
lean::dec(x_164);
x_194 = lean::cnstr_get(x_165, 0);
x_196 = lean::cnstr_get_scalar<uint8>(x_165, sizeof(void*)*1);
if (lean::is_exclusive(x_165)) {
 x_197 = x_165;
} else {
 lean::inc(x_194);
 lean::dec(x_165);
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
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_162, x_199);
if (lean::obj_tag(x_200) == 0)
{
obj* x_201; obj* x_203; obj* x_205; 
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_200, 1);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_200, 2);
lean::inc(x_205);
lean::dec(x_200);
x_152 = x_201;
x_153 = x_203;
x_154 = x_205;
goto lbl_155;
}
else
{
obj* x_208; uint8 x_210; obj* x_211; obj* x_213; obj* x_214; 
x_208 = lean::cnstr_get(x_200, 0);
x_210 = lean::cnstr_get_scalar<uint8>(x_200, sizeof(void*)*1);
if (lean::is_exclusive(x_200)) {
 x_211 = x_200;
} else {
 lean::inc(x_208);
 lean::dec(x_200);
 x_211 = lean::box(0);
}
lean::inc(x_208);
if (lean::is_scalar(x_211)) {
 x_213 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_213 = x_211;
}
lean::cnstr_set(x_213, 0, x_208);
lean::cnstr_set_scalar(x_213, sizeof(void*)*1, x_210);
x_214 = x_213;
x_148 = x_214;
x_149 = x_208;
x_150 = x_210;
goto lbl_151;
}
}
}
else
{
obj* x_215; uint8 x_217; obj* x_218; obj* x_220; obj* x_221; 
x_215 = lean::cnstr_get(x_159, 0);
x_217 = lean::cnstr_get_scalar<uint8>(x_159, sizeof(void*)*1);
if (lean::is_exclusive(x_159)) {
 x_218 = x_159;
} else {
 lean::inc(x_215);
 lean::dec(x_159);
 x_218 = lean::box(0);
}
lean::inc(x_215);
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_215);
lean::cnstr_set_scalar(x_220, sizeof(void*)*1, x_217);
x_221 = x_220;
x_148 = x_221;
x_149 = x_215;
x_150 = x_217;
goto lbl_151;
}
}
else
{
obj* x_226; obj* x_227; 
lean::dec(x_85);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_226 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_84);
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_226);
return x_227;
}
lbl_151:
{
obj* x_228; obj* x_229; uint8 x_230; obj* x_232; obj* x_233; obj* x_234; 
if (x_150 == 0)
{
obj* x_237; obj* x_239; 
lean::dec(x_148);
x_237 = l_lean_ir_parse__untyped__assignment___closed__4;
lean::inc(x_4);
x_239 = l_lean_ir_keyword(x_237, x_4);
if (lean::obj_tag(x_239) == 0)
{
obj* x_240; obj* x_242; obj* x_244; obj* x_245; 
x_240 = lean::cnstr_get(x_239, 1);
x_242 = lean::cnstr_get(x_239, 2);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 lean::cnstr_set(x_239, 1, lean::box(0));
 lean::cnstr_set(x_239, 2, lean::box(0));
 x_244 = x_239;
} else {
 lean::inc(x_240);
 lean::inc(x_242);
 lean::dec(x_239);
 x_244 = lean::box(0);
}
x_245 = l_lean_ir_parse__fnid(x_240);
if (lean::obj_tag(x_245) == 0)
{
obj* x_246; obj* x_248; obj* x_250; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; 
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 1);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_245, 2);
lean::inc(x_250);
lean::dec(x_245);
lean::inc(x_0);
x_254 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__4), 3, 2);
lean::closure_set(x_254, 0, x_0);
lean::closure_set(x_254, 1, x_246);
x_255 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_244)) {
 x_256 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_256 = x_244;
}
lean::cnstr_set(x_256, 0, x_254);
lean::cnstr_set(x_256, 1, x_248);
lean::cnstr_set(x_256, 2, x_255);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_256);
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_242, x_257);
if (lean::obj_tag(x_258) == 0)
{
obj* x_259; obj* x_261; obj* x_263; 
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_258, 2);
lean::inc(x_263);
lean::dec(x_258);
x_232 = x_259;
x_233 = x_261;
x_234 = x_263;
goto lbl_235;
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_271; obj* x_272; 
x_266 = lean::cnstr_get(x_258, 0);
x_268 = lean::cnstr_get_scalar<uint8>(x_258, sizeof(void*)*1);
if (lean::is_exclusive(x_258)) {
 x_269 = x_258;
} else {
 lean::inc(x_266);
 lean::dec(x_258);
 x_269 = lean::box(0);
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
x_228 = x_272;
x_229 = x_266;
x_230 = x_268;
goto lbl_231;
}
}
else
{
obj* x_274; uint8 x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
lean::dec(x_244);
x_274 = lean::cnstr_get(x_245, 0);
x_276 = lean::cnstr_get_scalar<uint8>(x_245, sizeof(void*)*1);
if (lean::is_exclusive(x_245)) {
 x_277 = x_245;
} else {
 lean::inc(x_274);
 lean::dec(x_245);
 x_277 = lean::box(0);
}
if (lean::is_scalar(x_277)) {
 x_278 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_278 = x_277;
}
lean::cnstr_set(x_278, 0, x_274);
lean::cnstr_set_scalar(x_278, sizeof(void*)*1, x_276);
x_279 = x_278;
x_280 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_242, x_279);
if (lean::obj_tag(x_280) == 0)
{
obj* x_281; obj* x_283; obj* x_285; 
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
x_285 = lean::cnstr_get(x_280, 2);
lean::inc(x_285);
lean::dec(x_280);
x_232 = x_281;
x_233 = x_283;
x_234 = x_285;
goto lbl_235;
}
else
{
obj* x_288; uint8 x_290; obj* x_291; obj* x_293; obj* x_294; 
x_288 = lean::cnstr_get(x_280, 0);
x_290 = lean::cnstr_get_scalar<uint8>(x_280, sizeof(void*)*1);
if (lean::is_exclusive(x_280)) {
 x_291 = x_280;
} else {
 lean::inc(x_288);
 lean::dec(x_280);
 x_291 = lean::box(0);
}
lean::inc(x_288);
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_288);
lean::cnstr_set_scalar(x_293, sizeof(void*)*1, x_290);
x_294 = x_293;
x_228 = x_294;
x_229 = x_288;
x_230 = x_290;
goto lbl_231;
}
}
}
else
{
obj* x_295; uint8 x_297; obj* x_298; obj* x_300; obj* x_301; 
x_295 = lean::cnstr_get(x_239, 0);
x_297 = lean::cnstr_get_scalar<uint8>(x_239, sizeof(void*)*1);
if (lean::is_exclusive(x_239)) {
 x_298 = x_239;
} else {
 lean::inc(x_295);
 lean::dec(x_239);
 x_298 = lean::box(0);
}
lean::inc(x_295);
if (lean::is_scalar(x_298)) {
 x_300 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_300 = x_298;
}
lean::cnstr_set(x_300, 0, x_295);
lean::cnstr_set_scalar(x_300, sizeof(void*)*1, x_297);
x_301 = x_300;
x_228 = x_301;
x_229 = x_295;
x_230 = x_297;
goto lbl_231;
}
}
else
{
obj* x_306; obj* x_307; obj* x_308; 
lean::dec(x_149);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_306 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_148);
x_307 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_306);
x_308 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_307);
return x_308;
}
lbl_231:
{
obj* x_309; obj* x_310; uint8 x_311; obj* x_313; obj* x_314; obj* x_315; obj* x_317; obj* x_318; obj* x_319; 
if (x_230 == 0)
{
obj* x_322; obj* x_324; 
lean::dec(x_228);
x_322 = l_lean_ir_parse__untyped__assignment___closed__3;
lean::inc(x_4);
x_324 = l_lean_ir_keyword(x_322, x_4);
if (lean::obj_tag(x_324) == 0)
{
obj* x_325; obj* x_327; obj* x_329; obj* x_330; 
x_325 = lean::cnstr_get(x_324, 1);
x_327 = lean::cnstr_get(x_324, 2);
if (lean::is_exclusive(x_324)) {
 lean::cnstr_release(x_324, 0);
 lean::cnstr_set(x_324, 1, lean::box(0));
 lean::cnstr_set(x_324, 2, lean::box(0));
 x_329 = x_324;
} else {
 lean::inc(x_325);
 lean::inc(x_327);
 lean::dec(x_324);
 x_329 = lean::box(0);
}
x_330 = l_lean_ir_parse__uint16(x_325);
if (lean::obj_tag(x_330) == 0)
{
obj* x_331; obj* x_333; obj* x_335; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
x_331 = lean::cnstr_get(x_330, 0);
lean::inc(x_331);
x_333 = lean::cnstr_get(x_330, 1);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_330, 2);
lean::inc(x_335);
lean::dec(x_330);
lean::inc(x_0);
x_339 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__3___boxed), 4, 2);
lean::closure_set(x_339, 0, x_0);
lean::closure_set(x_339, 1, x_331);
x_340 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_329)) {
 x_341 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_341 = x_329;
}
lean::cnstr_set(x_341, 0, x_339);
lean::cnstr_set(x_341, 1, x_333);
lean::cnstr_set(x_341, 2, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_335, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_327, x_342);
if (lean::obj_tag(x_343) == 0)
{
obj* x_344; obj* x_346; obj* x_348; 
x_344 = lean::cnstr_get(x_343, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_343, 1);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_343, 2);
lean::inc(x_348);
lean::dec(x_343);
x_317 = x_344;
x_318 = x_346;
x_319 = x_348;
goto lbl_320;
}
else
{
obj* x_351; uint8 x_353; obj* x_354; obj* x_356; obj* x_357; 
x_351 = lean::cnstr_get(x_343, 0);
x_353 = lean::cnstr_get_scalar<uint8>(x_343, sizeof(void*)*1);
if (lean::is_exclusive(x_343)) {
 x_354 = x_343;
} else {
 lean::inc(x_351);
 lean::dec(x_343);
 x_354 = lean::box(0);
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
x_309 = x_357;
x_310 = x_351;
x_311 = x_353;
goto lbl_312;
}
}
else
{
obj* x_359; uint8 x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
lean::dec(x_329);
x_359 = lean::cnstr_get(x_330, 0);
x_361 = lean::cnstr_get_scalar<uint8>(x_330, sizeof(void*)*1);
if (lean::is_exclusive(x_330)) {
 x_362 = x_330;
} else {
 lean::inc(x_359);
 lean::dec(x_330);
 x_362 = lean::box(0);
}
if (lean::is_scalar(x_362)) {
 x_363 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_363 = x_362;
}
lean::cnstr_set(x_363, 0, x_359);
lean::cnstr_set_scalar(x_363, sizeof(void*)*1, x_361);
x_364 = x_363;
x_365 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_327, x_364);
if (lean::obj_tag(x_365) == 0)
{
obj* x_366; obj* x_368; obj* x_370; 
x_366 = lean::cnstr_get(x_365, 0);
lean::inc(x_366);
x_368 = lean::cnstr_get(x_365, 1);
lean::inc(x_368);
x_370 = lean::cnstr_get(x_365, 2);
lean::inc(x_370);
lean::dec(x_365);
x_317 = x_366;
x_318 = x_368;
x_319 = x_370;
goto lbl_320;
}
else
{
obj* x_373; uint8 x_375; obj* x_376; obj* x_378; obj* x_379; 
x_373 = lean::cnstr_get(x_365, 0);
x_375 = lean::cnstr_get_scalar<uint8>(x_365, sizeof(void*)*1);
if (lean::is_exclusive(x_365)) {
 x_376 = x_365;
} else {
 lean::inc(x_373);
 lean::dec(x_365);
 x_376 = lean::box(0);
}
lean::inc(x_373);
if (lean::is_scalar(x_376)) {
 x_378 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_378 = x_376;
}
lean::cnstr_set(x_378, 0, x_373);
lean::cnstr_set_scalar(x_378, sizeof(void*)*1, x_375);
x_379 = x_378;
x_309 = x_379;
x_310 = x_373;
x_311 = x_375;
goto lbl_312;
}
}
}
else
{
obj* x_380; uint8 x_382; obj* x_383; obj* x_385; obj* x_386; 
x_380 = lean::cnstr_get(x_324, 0);
x_382 = lean::cnstr_get_scalar<uint8>(x_324, sizeof(void*)*1);
if (lean::is_exclusive(x_324)) {
 x_383 = x_324;
} else {
 lean::inc(x_380);
 lean::dec(x_324);
 x_383 = lean::box(0);
}
lean::inc(x_380);
if (lean::is_scalar(x_383)) {
 x_385 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_385 = x_383;
}
lean::cnstr_set(x_385, 0, x_380);
lean::cnstr_set_scalar(x_385, sizeof(void*)*1, x_382);
x_386 = x_385;
x_309 = x_386;
x_310 = x_380;
x_311 = x_382;
goto lbl_312;
}
}
else
{
obj* x_391; obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_229);
x_391 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_228);
x_392 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_391);
x_393 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_392);
x_394 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_393);
return x_394;
}
lbl_312:
{
obj* x_395; obj* x_396; uint8 x_397; obj* x_399; obj* x_400; obj* x_401; 
if (x_311 == 0)
{
obj* x_404; obj* x_406; 
lean::dec(x_309);
x_404 = l_lean_ir_parse__untyped__assignment___closed__2;
lean::inc(x_4);
x_406 = l_lean_ir_keyword(x_404, x_4);
if (lean::obj_tag(x_406) == 0)
{
obj* x_407; obj* x_409; obj* x_411; obj* x_412; 
x_407 = lean::cnstr_get(x_406, 1);
x_409 = lean::cnstr_get(x_406, 2);
if (lean::is_exclusive(x_406)) {
 lean::cnstr_release(x_406, 0);
 lean::cnstr_set(x_406, 1, lean::box(0));
 lean::cnstr_set(x_406, 2, lean::box(0));
 x_411 = x_406;
} else {
 lean::inc(x_407);
 lean::inc(x_409);
 lean::dec(x_406);
 x_411 = lean::box(0);
}
x_412 = l_lean_ir_parse__var(x_407);
if (lean::obj_tag(x_412) == 0)
{
obj* x_413; obj* x_415; obj* x_417; obj* x_421; obj* x_422; obj* x_423; obj* x_424; obj* x_425; 
x_413 = lean::cnstr_get(x_412, 0);
lean::inc(x_413);
x_415 = lean::cnstr_get(x_412, 1);
lean::inc(x_415);
x_417 = lean::cnstr_get(x_412, 2);
lean::inc(x_417);
lean::dec(x_412);
lean::inc(x_0);
x_421 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__2), 3, 2);
lean::closure_set(x_421, 0, x_0);
lean::closure_set(x_421, 1, x_413);
x_422 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_411)) {
 x_423 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_423 = x_411;
}
lean::cnstr_set(x_423, 0, x_421);
lean::cnstr_set(x_423, 1, x_415);
lean::cnstr_set(x_423, 2, x_422);
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_417, x_423);
x_425 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_424);
if (lean::obj_tag(x_425) == 0)
{
obj* x_426; obj* x_428; obj* x_430; 
x_426 = lean::cnstr_get(x_425, 0);
lean::inc(x_426);
x_428 = lean::cnstr_get(x_425, 1);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_425, 2);
lean::inc(x_430);
lean::dec(x_425);
x_399 = x_426;
x_400 = x_428;
x_401 = x_430;
goto lbl_402;
}
else
{
obj* x_433; uint8 x_435; obj* x_436; obj* x_438; obj* x_439; 
x_433 = lean::cnstr_get(x_425, 0);
x_435 = lean::cnstr_get_scalar<uint8>(x_425, sizeof(void*)*1);
if (lean::is_exclusive(x_425)) {
 x_436 = x_425;
} else {
 lean::inc(x_433);
 lean::dec(x_425);
 x_436 = lean::box(0);
}
lean::inc(x_433);
if (lean::is_scalar(x_436)) {
 x_438 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_438 = x_436;
}
lean::cnstr_set(x_438, 0, x_433);
lean::cnstr_set_scalar(x_438, sizeof(void*)*1, x_435);
x_439 = x_438;
x_395 = x_439;
x_396 = x_433;
x_397 = x_435;
goto lbl_398;
}
}
else
{
obj* x_441; uint8 x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; 
lean::dec(x_411);
x_441 = lean::cnstr_get(x_412, 0);
x_443 = lean::cnstr_get_scalar<uint8>(x_412, sizeof(void*)*1);
if (lean::is_exclusive(x_412)) {
 x_444 = x_412;
} else {
 lean::inc(x_441);
 lean::dec(x_412);
 x_444 = lean::box(0);
}
if (lean::is_scalar(x_444)) {
 x_445 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_445 = x_444;
}
lean::cnstr_set(x_445, 0, x_441);
lean::cnstr_set_scalar(x_445, sizeof(void*)*1, x_443);
x_446 = x_445;
x_447 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_446);
if (lean::obj_tag(x_447) == 0)
{
obj* x_448; obj* x_450; obj* x_452; 
x_448 = lean::cnstr_get(x_447, 0);
lean::inc(x_448);
x_450 = lean::cnstr_get(x_447, 1);
lean::inc(x_450);
x_452 = lean::cnstr_get(x_447, 2);
lean::inc(x_452);
lean::dec(x_447);
x_399 = x_448;
x_400 = x_450;
x_401 = x_452;
goto lbl_402;
}
else
{
obj* x_455; uint8 x_457; obj* x_458; obj* x_460; obj* x_461; 
x_455 = lean::cnstr_get(x_447, 0);
x_457 = lean::cnstr_get_scalar<uint8>(x_447, sizeof(void*)*1);
if (lean::is_exclusive(x_447)) {
 x_458 = x_447;
} else {
 lean::inc(x_455);
 lean::dec(x_447);
 x_458 = lean::box(0);
}
lean::inc(x_455);
if (lean::is_scalar(x_458)) {
 x_460 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_460 = x_458;
}
lean::cnstr_set(x_460, 0, x_455);
lean::cnstr_set_scalar(x_460, sizeof(void*)*1, x_457);
x_461 = x_460;
x_395 = x_461;
x_396 = x_455;
x_397 = x_457;
goto lbl_398;
}
}
}
else
{
obj* x_462; uint8 x_464; obj* x_465; obj* x_467; obj* x_468; 
x_462 = lean::cnstr_get(x_406, 0);
x_464 = lean::cnstr_get_scalar<uint8>(x_406, sizeof(void*)*1);
if (lean::is_exclusive(x_406)) {
 x_465 = x_406;
} else {
 lean::inc(x_462);
 lean::dec(x_406);
 x_465 = lean::box(0);
}
lean::inc(x_462);
if (lean::is_scalar(x_465)) {
 x_467 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_467 = x_465;
}
lean::cnstr_set(x_467, 0, x_462);
lean::cnstr_set_scalar(x_467, sizeof(void*)*1, x_464);
x_468 = x_467;
x_395 = x_468;
x_396 = x_462;
x_397 = x_464;
goto lbl_398;
}
}
else
{
obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_310);
x_473 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_309);
x_474 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_473);
x_475 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_474);
x_476 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_475);
x_477 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_476);
return x_477;
}
lbl_398:
{
obj* x_478; obj* x_479; obj* x_480; obj* x_482; obj* x_483; obj* x_484; 
if (x_397 == 0)
{
obj* x_487; obj* x_488; 
lean::dec(x_395);
x_487 = l_lean_ir_parse__untyped__assignment___closed__1;
x_488 = l_lean_ir_keyword(x_487, x_4);
if (lean::obj_tag(x_488) == 0)
{
obj* x_489; obj* x_491; obj* x_493; obj* x_494; obj* x_495; obj* x_496; 
x_489 = lean::cnstr_get(x_488, 1);
x_491 = lean::cnstr_get(x_488, 2);
if (lean::is_exclusive(x_488)) {
 lean::cnstr_release(x_488, 0);
 lean::cnstr_set(x_488, 1, lean::box(0));
 lean::cnstr_set(x_488, 2, lean::box(0));
 x_493 = x_488;
} else {
 lean::inc(x_489);
 lean::inc(x_491);
 lean::dec(x_488);
 x_493 = lean::box(0);
}
x_494 = l_lean_ir_parse__typed__assignment___closed__2;
x_495 = l_lean_ir_str2type;
x_496 = l_lean_ir_parse__key2val___main___rarg(x_494, x_495, x_489);
if (lean::obj_tag(x_496) == 0)
{
obj* x_497; obj* x_499; obj* x_501; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; 
x_497 = lean::cnstr_get(x_496, 0);
lean::inc(x_497);
x_499 = lean::cnstr_get(x_496, 1);
lean::inc(x_499);
x_501 = lean::cnstr_get(x_496, 2);
lean::inc(x_501);
lean::dec(x_496);
x_504 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__1___boxed), 4, 2);
lean::closure_set(x_504, 0, x_0);
lean::closure_set(x_504, 1, x_497);
x_505 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_493)) {
 x_506 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_506 = x_493;
}
lean::cnstr_set(x_506, 0, x_504);
lean::cnstr_set(x_506, 1, x_499);
lean::cnstr_set(x_506, 2, x_505);
x_507 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_501, x_506);
x_508 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_491, x_507);
if (lean::obj_tag(x_508) == 0)
{
obj* x_509; obj* x_511; obj* x_513; 
x_509 = lean::cnstr_get(x_508, 0);
lean::inc(x_509);
x_511 = lean::cnstr_get(x_508, 1);
lean::inc(x_511);
x_513 = lean::cnstr_get(x_508, 2);
lean::inc(x_513);
lean::dec(x_508);
x_482 = x_509;
x_483 = x_511;
x_484 = x_513;
goto lbl_485;
}
else
{
obj* x_517; uint8 x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; 
lean::dec(x_8);
x_517 = lean::cnstr_get(x_508, 0);
x_519 = lean::cnstr_get_scalar<uint8>(x_508, sizeof(void*)*1);
if (lean::is_exclusive(x_508)) {
 x_520 = x_508;
} else {
 lean::inc(x_517);
 lean::dec(x_508);
 x_520 = lean::box(0);
}
if (lean::is_scalar(x_520)) {
 x_521 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_521 = x_520;
}
lean::cnstr_set(x_521, 0, x_517);
lean::cnstr_set_scalar(x_521, sizeof(void*)*1, x_519);
x_522 = x_521;
x_523 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_522);
x_524 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_523);
x_525 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_524);
x_526 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_525);
x_527 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_526);
x_528 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_527);
x_529 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_528);
return x_529;
}
}
else
{
obj* x_532; uint8 x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; 
lean::dec(x_493);
lean::dec(x_0);
x_532 = lean::cnstr_get(x_496, 0);
x_534 = lean::cnstr_get_scalar<uint8>(x_496, sizeof(void*)*1);
if (lean::is_exclusive(x_496)) {
 x_535 = x_496;
} else {
 lean::inc(x_532);
 lean::dec(x_496);
 x_535 = lean::box(0);
}
if (lean::is_scalar(x_535)) {
 x_536 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_536 = x_535;
}
lean::cnstr_set(x_536, 0, x_532);
lean::cnstr_set_scalar(x_536, sizeof(void*)*1, x_534);
x_537 = x_536;
x_538 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_491, x_537);
if (lean::obj_tag(x_538) == 0)
{
obj* x_539; obj* x_541; obj* x_543; 
x_539 = lean::cnstr_get(x_538, 0);
lean::inc(x_539);
x_541 = lean::cnstr_get(x_538, 1);
lean::inc(x_541);
x_543 = lean::cnstr_get(x_538, 2);
lean::inc(x_543);
lean::dec(x_538);
x_482 = x_539;
x_483 = x_541;
x_484 = x_543;
goto lbl_485;
}
else
{
obj* x_547; uint8 x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; 
lean::dec(x_8);
x_547 = lean::cnstr_get(x_538, 0);
x_549 = lean::cnstr_get_scalar<uint8>(x_538, sizeof(void*)*1);
if (lean::is_exclusive(x_538)) {
 x_550 = x_538;
} else {
 lean::inc(x_547);
 lean::dec(x_538);
 x_550 = lean::box(0);
}
if (lean::is_scalar(x_550)) {
 x_551 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_551 = x_550;
}
lean::cnstr_set(x_551, 0, x_547);
lean::cnstr_set_scalar(x_551, sizeof(void*)*1, x_549);
x_552 = x_551;
x_553 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_552);
x_554 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_553);
x_555 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_554);
x_556 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_555);
x_557 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_556);
x_558 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_557);
x_559 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_558);
return x_559;
}
}
}
else
{
obj* x_562; uint8 x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_574; 
lean::dec(x_8);
lean::dec(x_0);
x_562 = lean::cnstr_get(x_488, 0);
x_564 = lean::cnstr_get_scalar<uint8>(x_488, sizeof(void*)*1);
if (lean::is_exclusive(x_488)) {
 x_565 = x_488;
} else {
 lean::inc(x_562);
 lean::dec(x_488);
 x_565 = lean::box(0);
}
if (lean::is_scalar(x_565)) {
 x_566 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_566 = x_565;
}
lean::cnstr_set(x_566, 0, x_562);
lean::cnstr_set_scalar(x_566, sizeof(void*)*1, x_564);
x_567 = x_566;
x_568 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_567);
x_569 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_568);
x_570 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_569);
x_571 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_570);
x_572 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_571);
x_573 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_572);
x_574 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_573);
return x_574;
}
}
else
{
obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; 
lean::dec(x_396);
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_395);
x_580 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_579);
x_581 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_580);
x_582 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_581);
x_583 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_582);
x_584 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_583);
return x_584;
}
lbl_481:
{
obj* x_585; 
x_585 = l_lean_ir_parse__var(x_479);
if (lean::obj_tag(x_585) == 0)
{
obj* x_586; obj* x_588; obj* x_590; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; 
x_586 = lean::cnstr_get(x_585, 0);
lean::inc(x_586);
x_588 = lean::cnstr_get(x_585, 1);
lean::inc(x_588);
x_590 = lean::cnstr_get(x_585, 2);
lean::inc(x_590);
lean::dec(x_585);
x_593 = lean::apply_1(x_478, x_586);
x_594 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_595 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_595 = x_8;
}
lean::cnstr_set(x_595, 0, x_593);
lean::cnstr_set(x_595, 1, x_588);
lean::cnstr_set(x_595, 2, x_594);
x_596 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_590, x_595);
x_597 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_480, x_596);
x_598 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_597);
x_599 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_598);
x_600 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_599);
x_601 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_600);
x_602 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_601);
x_603 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_602);
x_604 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_603);
return x_604;
}
else
{
obj* x_607; uint8 x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; obj* x_620; 
lean::dec(x_478);
lean::dec(x_8);
x_607 = lean::cnstr_get(x_585, 0);
x_609 = lean::cnstr_get_scalar<uint8>(x_585, sizeof(void*)*1);
if (lean::is_exclusive(x_585)) {
 x_610 = x_585;
} else {
 lean::inc(x_607);
 lean::dec(x_585);
 x_610 = lean::box(0);
}
if (lean::is_scalar(x_610)) {
 x_611 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_611 = x_610;
}
lean::cnstr_set(x_611, 0, x_607);
lean::cnstr_set_scalar(x_611, sizeof(void*)*1, x_609);
x_612 = x_611;
x_613 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_480, x_612);
x_614 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_613);
x_615 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_614);
x_616 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_615);
x_617 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_616);
x_618 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_617);
x_619 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_618);
x_620 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_619);
return x_620;
}
}
lbl_485:
{
obj* x_621; 
x_621 = l_lean_ir_parse__var(x_483);
if (lean::obj_tag(x_621) == 0)
{
obj* x_622; obj* x_624; obj* x_626; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; 
x_622 = lean::cnstr_get(x_621, 0);
x_624 = lean::cnstr_get(x_621, 1);
x_626 = lean::cnstr_get(x_621, 2);
if (lean::is_exclusive(x_621)) {
 x_628 = x_621;
} else {
 lean::inc(x_622);
 lean::inc(x_624);
 lean::inc(x_626);
 lean::dec(x_621);
 x_628 = lean::box(0);
}
x_629 = lean::apply_1(x_482, x_622);
x_630 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_628)) {
 x_631 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_631 = x_628;
}
lean::cnstr_set(x_631, 0, x_629);
lean::cnstr_set(x_631, 1, x_624);
lean::cnstr_set(x_631, 2, x_630);
x_632 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_626, x_631);
x_633 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_484, x_632);
if (lean::obj_tag(x_633) == 0)
{
obj* x_634; obj* x_636; obj* x_638; 
x_634 = lean::cnstr_get(x_633, 0);
lean::inc(x_634);
x_636 = lean::cnstr_get(x_633, 1);
lean::inc(x_636);
x_638 = lean::cnstr_get(x_633, 2);
lean::inc(x_638);
lean::dec(x_633);
x_478 = x_634;
x_479 = x_636;
x_480 = x_638;
goto lbl_481;
}
else
{
obj* x_642; uint8 x_644; obj* x_645; obj* x_646; obj* x_647; obj* x_648; obj* x_649; obj* x_650; obj* x_651; obj* x_652; obj* x_653; obj* x_654; 
lean::dec(x_8);
x_642 = lean::cnstr_get(x_633, 0);
x_644 = lean::cnstr_get_scalar<uint8>(x_633, sizeof(void*)*1);
if (lean::is_exclusive(x_633)) {
 x_645 = x_633;
} else {
 lean::inc(x_642);
 lean::dec(x_633);
 x_645 = lean::box(0);
}
if (lean::is_scalar(x_645)) {
 x_646 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_646 = x_645;
}
lean::cnstr_set(x_646, 0, x_642);
lean::cnstr_set_scalar(x_646, sizeof(void*)*1, x_644);
x_647 = x_646;
x_648 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_647);
x_649 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_648);
x_650 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_649);
x_651 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_650);
x_652 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_651);
x_653 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_652);
x_654 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_653);
return x_654;
}
}
else
{
obj* x_656; uint8 x_658; obj* x_659; obj* x_660; obj* x_661; obj* x_662; 
lean::dec(x_482);
x_656 = lean::cnstr_get(x_621, 0);
x_658 = lean::cnstr_get_scalar<uint8>(x_621, sizeof(void*)*1);
if (lean::is_exclusive(x_621)) {
 x_659 = x_621;
} else {
 lean::inc(x_656);
 lean::dec(x_621);
 x_659 = lean::box(0);
}
if (lean::is_scalar(x_659)) {
 x_660 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_660 = x_659;
}
lean::cnstr_set(x_660, 0, x_656);
lean::cnstr_set_scalar(x_660, sizeof(void*)*1, x_658);
x_661 = x_660;
x_662 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_484, x_661);
if (lean::obj_tag(x_662) == 0)
{
obj* x_663; obj* x_665; obj* x_667; 
x_663 = lean::cnstr_get(x_662, 0);
lean::inc(x_663);
x_665 = lean::cnstr_get(x_662, 1);
lean::inc(x_665);
x_667 = lean::cnstr_get(x_662, 2);
lean::inc(x_667);
lean::dec(x_662);
x_478 = x_663;
x_479 = x_665;
x_480 = x_667;
goto lbl_481;
}
else
{
obj* x_671; uint8 x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; obj* x_682; obj* x_683; 
lean::dec(x_8);
x_671 = lean::cnstr_get(x_662, 0);
x_673 = lean::cnstr_get_scalar<uint8>(x_662, sizeof(void*)*1);
if (lean::is_exclusive(x_662)) {
 x_674 = x_662;
} else {
 lean::inc(x_671);
 lean::dec(x_662);
 x_674 = lean::box(0);
}
if (lean::is_scalar(x_674)) {
 x_675 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_675 = x_674;
}
lean::cnstr_set(x_675, 0, x_671);
lean::cnstr_set_scalar(x_675, sizeof(void*)*1, x_673);
x_676 = x_675;
x_677 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_396, x_676);
x_678 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_677);
x_679 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_678);
x_680 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_679);
x_681 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_680);
x_682 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_681);
x_683 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_682);
return x_683;
}
}
}
}
lbl_402:
{
obj* x_684; 
x_684 = l_lean_ir_parse__var(x_400);
if (lean::obj_tag(x_684) == 0)
{
obj* x_685; obj* x_687; obj* x_689; obj* x_691; obj* x_692; obj* x_693; obj* x_694; obj* x_695; obj* x_696; 
x_685 = lean::cnstr_get(x_684, 0);
x_687 = lean::cnstr_get(x_684, 1);
x_689 = lean::cnstr_get(x_684, 2);
if (lean::is_exclusive(x_684)) {
 x_691 = x_684;
} else {
 lean::inc(x_685);
 lean::inc(x_687);
 lean::inc(x_689);
 lean::dec(x_684);
 x_691 = lean::box(0);
}
x_692 = lean::apply_1(x_399, x_685);
x_693 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_691)) {
 x_694 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_694 = x_691;
}
lean::cnstr_set(x_694, 0, x_692);
lean::cnstr_set(x_694, 1, x_687);
lean::cnstr_set(x_694, 2, x_693);
x_695 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_689, x_694);
x_696 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_695);
if (lean::obj_tag(x_696) == 0)
{
obj* x_700; obj* x_701; obj* x_702; obj* x_703; obj* x_704; obj* x_705; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_700 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_696);
x_701 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_700);
x_702 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_701);
x_703 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_702);
x_704 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_703);
x_705 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_704);
return x_705;
}
else
{
obj* x_706; uint8 x_708; 
x_706 = lean::cnstr_get(x_696, 0);
lean::inc(x_706);
x_708 = lean::cnstr_get_scalar<uint8>(x_696, sizeof(void*)*1);
x_395 = x_696;
x_396 = x_706;
x_397 = x_708;
goto lbl_398;
}
}
else
{
obj* x_710; uint8 x_712; obj* x_713; obj* x_714; obj* x_715; obj* x_716; 
lean::dec(x_399);
x_710 = lean::cnstr_get(x_684, 0);
x_712 = lean::cnstr_get_scalar<uint8>(x_684, sizeof(void*)*1);
if (lean::is_exclusive(x_684)) {
 x_713 = x_684;
} else {
 lean::inc(x_710);
 lean::dec(x_684);
 x_713 = lean::box(0);
}
if (lean::is_scalar(x_713)) {
 x_714 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_714 = x_713;
}
lean::cnstr_set(x_714, 0, x_710);
lean::cnstr_set_scalar(x_714, sizeof(void*)*1, x_712);
x_715 = x_714;
x_716 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_715);
if (lean::obj_tag(x_716) == 0)
{
obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; obj* x_725; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_720 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_310, x_716);
x_721 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_720);
x_722 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_721);
x_723 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_722);
x_724 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_723);
x_725 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_724);
return x_725;
}
else
{
obj* x_726; uint8 x_728; 
x_726 = lean::cnstr_get(x_716, 0);
lean::inc(x_726);
x_728 = lean::cnstr_get_scalar<uint8>(x_716, sizeof(void*)*1);
x_395 = x_716;
x_396 = x_726;
x_397 = x_728;
goto lbl_398;
}
}
}
}
lbl_316:
{
obj* x_729; 
x_729 = l_lean_ir_parse__usize(x_314);
if (lean::obj_tag(x_729) == 0)
{
obj* x_730; obj* x_732; obj* x_734; obj* x_736; obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; 
x_730 = lean::cnstr_get(x_729, 0);
x_732 = lean::cnstr_get(x_729, 1);
x_734 = lean::cnstr_get(x_729, 2);
if (lean::is_exclusive(x_729)) {
 x_736 = x_729;
} else {
 lean::inc(x_730);
 lean::inc(x_732);
 lean::inc(x_734);
 lean::dec(x_729);
 x_736 = lean::box(0);
}
x_737 = lean::apply_1(x_313, x_730);
x_738 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_736)) {
 x_739 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_739 = x_736;
}
lean::cnstr_set(x_739, 0, x_737);
lean::cnstr_set(x_739, 1, x_732);
lean::cnstr_set(x_739, 2, x_738);
x_740 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_734, x_739);
x_741 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_315, x_740);
if (lean::obj_tag(x_741) == 0)
{
obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_745 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_741);
x_746 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_745);
x_747 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_746);
x_748 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_747);
x_749 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_748);
return x_749;
}
else
{
obj* x_750; uint8 x_752; 
x_750 = lean::cnstr_get(x_741, 0);
lean::inc(x_750);
x_752 = lean::cnstr_get_scalar<uint8>(x_741, sizeof(void*)*1);
x_309 = x_741;
x_310 = x_750;
x_311 = x_752;
goto lbl_312;
}
}
else
{
obj* x_754; uint8 x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; 
lean::dec(x_313);
x_754 = lean::cnstr_get(x_729, 0);
x_756 = lean::cnstr_get_scalar<uint8>(x_729, sizeof(void*)*1);
if (lean::is_exclusive(x_729)) {
 x_757 = x_729;
} else {
 lean::inc(x_754);
 lean::dec(x_729);
 x_757 = lean::box(0);
}
if (lean::is_scalar(x_757)) {
 x_758 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_758 = x_757;
}
lean::cnstr_set(x_758, 0, x_754);
lean::cnstr_set_scalar(x_758, sizeof(void*)*1, x_756);
x_759 = x_758;
x_760 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_315, x_759);
if (lean::obj_tag(x_760) == 0)
{
obj* x_764; obj* x_765; obj* x_766; obj* x_767; obj* x_768; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_764 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_229, x_760);
x_765 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_764);
x_766 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_765);
x_767 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_766);
x_768 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_767);
return x_768;
}
else
{
obj* x_769; uint8 x_771; 
x_769 = lean::cnstr_get(x_760, 0);
lean::inc(x_769);
x_771 = lean::cnstr_get_scalar<uint8>(x_760, sizeof(void*)*1);
x_309 = x_760;
x_310 = x_769;
x_311 = x_771;
goto lbl_312;
}
}
}
lbl_320:
{
obj* x_772; 
x_772 = l_lean_ir_parse__uint16(x_318);
if (lean::obj_tag(x_772) == 0)
{
obj* x_773; obj* x_775; obj* x_777; obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; obj* x_784; 
x_773 = lean::cnstr_get(x_772, 0);
x_775 = lean::cnstr_get(x_772, 1);
x_777 = lean::cnstr_get(x_772, 2);
if (lean::is_exclusive(x_772)) {
 x_779 = x_772;
} else {
 lean::inc(x_773);
 lean::inc(x_775);
 lean::inc(x_777);
 lean::dec(x_772);
 x_779 = lean::box(0);
}
x_780 = lean::apply_1(x_317, x_773);
x_781 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_779)) {
 x_782 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_782 = x_779;
}
lean::cnstr_set(x_782, 0, x_780);
lean::cnstr_set(x_782, 1, x_775);
lean::cnstr_set(x_782, 2, x_781);
x_783 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_777, x_782);
x_784 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_319, x_783);
if (lean::obj_tag(x_784) == 0)
{
obj* x_785; obj* x_787; obj* x_789; 
x_785 = lean::cnstr_get(x_784, 0);
lean::inc(x_785);
x_787 = lean::cnstr_get(x_784, 1);
lean::inc(x_787);
x_789 = lean::cnstr_get(x_784, 2);
lean::inc(x_789);
lean::dec(x_784);
x_313 = x_785;
x_314 = x_787;
x_315 = x_789;
goto lbl_316;
}
else
{
obj* x_792; uint8 x_794; obj* x_795; obj* x_797; obj* x_798; 
x_792 = lean::cnstr_get(x_784, 0);
x_794 = lean::cnstr_get_scalar<uint8>(x_784, sizeof(void*)*1);
if (lean::is_exclusive(x_784)) {
 x_795 = x_784;
} else {
 lean::inc(x_792);
 lean::dec(x_784);
 x_795 = lean::box(0);
}
lean::inc(x_792);
if (lean::is_scalar(x_795)) {
 x_797 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_797 = x_795;
}
lean::cnstr_set(x_797, 0, x_792);
lean::cnstr_set_scalar(x_797, sizeof(void*)*1, x_794);
x_798 = x_797;
x_309 = x_798;
x_310 = x_792;
x_311 = x_794;
goto lbl_312;
}
}
else
{
obj* x_800; uint8 x_802; obj* x_803; obj* x_804; obj* x_805; obj* x_806; 
lean::dec(x_317);
x_800 = lean::cnstr_get(x_772, 0);
x_802 = lean::cnstr_get_scalar<uint8>(x_772, sizeof(void*)*1);
if (lean::is_exclusive(x_772)) {
 x_803 = x_772;
} else {
 lean::inc(x_800);
 lean::dec(x_772);
 x_803 = lean::box(0);
}
if (lean::is_scalar(x_803)) {
 x_804 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_804 = x_803;
}
lean::cnstr_set(x_804, 0, x_800);
lean::cnstr_set_scalar(x_804, sizeof(void*)*1, x_802);
x_805 = x_804;
x_806 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_319, x_805);
if (lean::obj_tag(x_806) == 0)
{
obj* x_807; obj* x_809; obj* x_811; 
x_807 = lean::cnstr_get(x_806, 0);
lean::inc(x_807);
x_809 = lean::cnstr_get(x_806, 1);
lean::inc(x_809);
x_811 = lean::cnstr_get(x_806, 2);
lean::inc(x_811);
lean::dec(x_806);
x_313 = x_807;
x_314 = x_809;
x_315 = x_811;
goto lbl_316;
}
else
{
obj* x_814; uint8 x_816; obj* x_817; obj* x_819; obj* x_820; 
x_814 = lean::cnstr_get(x_806, 0);
x_816 = lean::cnstr_get_scalar<uint8>(x_806, sizeof(void*)*1);
if (lean::is_exclusive(x_806)) {
 x_817 = x_806;
} else {
 lean::inc(x_814);
 lean::dec(x_806);
 x_817 = lean::box(0);
}
lean::inc(x_814);
if (lean::is_scalar(x_817)) {
 x_819 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_819 = x_817;
}
lean::cnstr_set(x_819, 0, x_814);
lean::cnstr_set_scalar(x_819, sizeof(void*)*1, x_816);
x_820 = x_819;
x_309 = x_820;
x_310 = x_814;
x_311 = x_816;
goto lbl_312;
}
}
}
}
lbl_235:
{
obj* x_821; 
x_821 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(x_233);
if (lean::obj_tag(x_821) == 0)
{
obj* x_822; obj* x_824; obj* x_826; obj* x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; 
x_822 = lean::cnstr_get(x_821, 0);
x_824 = lean::cnstr_get(x_821, 1);
x_826 = lean::cnstr_get(x_821, 2);
if (lean::is_exclusive(x_821)) {
 x_828 = x_821;
} else {
 lean::inc(x_822);
 lean::inc(x_824);
 lean::inc(x_826);
 lean::dec(x_821);
 x_828 = lean::box(0);
}
x_829 = lean::apply_1(x_232, x_822);
x_830 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_828)) {
 x_831 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_831 = x_828;
}
lean::cnstr_set(x_831, 0, x_829);
lean::cnstr_set(x_831, 1, x_824);
lean::cnstr_set(x_831, 2, x_830);
x_832 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_826, x_831);
x_833 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_234, x_832);
if (lean::obj_tag(x_833) == 0)
{
obj* x_837; obj* x_838; obj* x_839; obj* x_840; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_837 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_833);
x_838 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_837);
x_839 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_838);
x_840 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_839);
return x_840;
}
else
{
obj* x_841; uint8 x_843; 
x_841 = lean::cnstr_get(x_833, 0);
lean::inc(x_841);
x_843 = lean::cnstr_get_scalar<uint8>(x_833, sizeof(void*)*1);
x_228 = x_833;
x_229 = x_841;
x_230 = x_843;
goto lbl_231;
}
}
else
{
obj* x_845; uint8 x_847; obj* x_848; obj* x_849; obj* x_850; obj* x_851; 
lean::dec(x_232);
x_845 = lean::cnstr_get(x_821, 0);
x_847 = lean::cnstr_get_scalar<uint8>(x_821, sizeof(void*)*1);
if (lean::is_exclusive(x_821)) {
 x_848 = x_821;
} else {
 lean::inc(x_845);
 lean::dec(x_821);
 x_848 = lean::box(0);
}
if (lean::is_scalar(x_848)) {
 x_849 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_849 = x_848;
}
lean::cnstr_set(x_849, 0, x_845);
lean::cnstr_set_scalar(x_849, sizeof(void*)*1, x_847);
x_850 = x_849;
x_851 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_234, x_850);
if (lean::obj_tag(x_851) == 0)
{
obj* x_855; obj* x_856; obj* x_857; obj* x_858; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_855 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_149, x_851);
x_856 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_855);
x_857 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_856);
x_858 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_857);
return x_858;
}
else
{
obj* x_859; uint8 x_861; 
x_859 = lean::cnstr_get(x_851, 0);
lean::inc(x_859);
x_861 = lean::cnstr_get_scalar<uint8>(x_851, sizeof(void*)*1);
x_228 = x_851;
x_229 = x_859;
x_230 = x_861;
goto lbl_231;
}
}
}
}
lbl_155:
{
obj* x_862; 
x_862 = l_lean_ir_parse__uint16(x_153);
if (lean::obj_tag(x_862) == 0)
{
obj* x_863; obj* x_865; obj* x_867; obj* x_869; obj* x_870; obj* x_871; obj* x_872; obj* x_873; obj* x_874; 
x_863 = lean::cnstr_get(x_862, 0);
x_865 = lean::cnstr_get(x_862, 1);
x_867 = lean::cnstr_get(x_862, 2);
if (lean::is_exclusive(x_862)) {
 x_869 = x_862;
} else {
 lean::inc(x_863);
 lean::inc(x_865);
 lean::inc(x_867);
 lean::dec(x_862);
 x_869 = lean::box(0);
}
x_870 = lean::apply_1(x_152, x_863);
x_871 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_869)) {
 x_872 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_872 = x_869;
}
lean::cnstr_set(x_872, 0, x_870);
lean::cnstr_set(x_872, 1, x_865);
lean::cnstr_set(x_872, 2, x_871);
x_873 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_867, x_872);
x_874 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_154, x_873);
if (lean::obj_tag(x_874) == 0)
{
obj* x_878; obj* x_879; obj* x_880; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_878 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_874);
x_879 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_878);
x_880 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_879);
return x_880;
}
else
{
obj* x_881; uint8 x_883; 
x_881 = lean::cnstr_get(x_874, 0);
lean::inc(x_881);
x_883 = lean::cnstr_get_scalar<uint8>(x_874, sizeof(void*)*1);
x_148 = x_874;
x_149 = x_881;
x_150 = x_883;
goto lbl_151;
}
}
else
{
obj* x_885; uint8 x_887; obj* x_888; obj* x_889; obj* x_890; obj* x_891; 
lean::dec(x_152);
x_885 = lean::cnstr_get(x_862, 0);
x_887 = lean::cnstr_get_scalar<uint8>(x_862, sizeof(void*)*1);
if (lean::is_exclusive(x_862)) {
 x_888 = x_862;
} else {
 lean::inc(x_885);
 lean::dec(x_862);
 x_888 = lean::box(0);
}
if (lean::is_scalar(x_888)) {
 x_889 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_889 = x_888;
}
lean::cnstr_set(x_889, 0, x_885);
lean::cnstr_set_scalar(x_889, sizeof(void*)*1, x_887);
x_890 = x_889;
x_891 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_154, x_890);
if (lean::obj_tag(x_891) == 0)
{
obj* x_895; obj* x_896; obj* x_897; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_0);
x_895 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_85, x_891);
x_896 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_81, x_895);
x_897 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_896);
return x_897;
}
else
{
obj* x_898; uint8 x_900; 
x_898 = lean::cnstr_get(x_891, 0);
lean::inc(x_898);
x_900 = lean::cnstr_get_scalar<uint8>(x_891, sizeof(void*)*1);
x_148 = x_891;
x_149 = x_898;
x_150 = x_900;
goto lbl_151;
}
}
}
}
}
}
lbl_14:
{
obj* x_901; 
x_901 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(x_12);
if (lean::obj_tag(x_901) == 0)
{
obj* x_902; obj* x_904; obj* x_906; obj* x_908; obj* x_909; obj* x_910; obj* x_911; obj* x_912; obj* x_913; 
x_902 = lean::cnstr_get(x_901, 0);
x_904 = lean::cnstr_get(x_901, 1);
x_906 = lean::cnstr_get(x_901, 2);
if (lean::is_exclusive(x_901)) {
 x_908 = x_901;
} else {
 lean::inc(x_902);
 lean::inc(x_904);
 lean::inc(x_906);
 lean::dec(x_901);
 x_908 = lean::box(0);
}
x_909 = lean::apply_1(x_11, x_902);
x_910 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_908)) {
 x_911 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_911 = x_908;
}
lean::cnstr_set(x_911, 0, x_909);
lean::cnstr_set(x_911, 1, x_904);
lean::cnstr_set(x_911, 2, x_910);
x_912 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_906, x_911);
x_913 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_912);
x_9 = x_913;
goto lbl_10;
}
else
{
obj* x_915; uint8 x_917; obj* x_918; obj* x_919; obj* x_920; obj* x_921; 
lean::dec(x_11);
x_915 = lean::cnstr_get(x_901, 0);
x_917 = lean::cnstr_get_scalar<uint8>(x_901, sizeof(void*)*1);
if (lean::is_exclusive(x_901)) {
 x_918 = x_901;
} else {
 lean::inc(x_915);
 lean::dec(x_901);
 x_918 = lean::box(0);
}
if (lean::is_scalar(x_918)) {
 x_919 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_919 = x_918;
}
lean::cnstr_set(x_919, 0, x_915);
lean::cnstr_set_scalar(x_919, sizeof(void*)*1, x_917);
x_920 = x_919;
x_921 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_920);
x_9 = x_921;
goto lbl_10;
}
}
}
else
{
obj* x_923; uint8 x_925; obj* x_926; obj* x_927; obj* x_928; 
lean::dec(x_0);
x_923 = lean::cnstr_get(x_3, 0);
x_925 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_926 = x_3;
} else {
 lean::inc(x_923);
 lean::dec(x_3);
 x_926 = lean::box(0);
}
if (lean::is_scalar(x_926)) {
 x_927 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_927 = x_926;
}
lean::cnstr_set(x_927, 0, x_923);
lean::cnstr_set_scalar(x_927, sizeof(void*)*1, x_925);
x_928 = x_927;
return x_928;
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
obj* x_88; obj* x_89; obj* x_91; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_88 = x_1;
} else {
 lean::dec(x_1);
 x_88 = lean::box(0);
}
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
obj* x_111; obj* x_113; obj* x_115; 
lean::dec(x_88);
x_111 = lean::cnstr_get(x_109, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_109, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_109, 2);
lean::inc(x_115);
lean::dec(x_109);
x_84 = x_111;
x_85 = x_113;
x_86 = x_115;
goto lbl_87;
}
else
{
obj* x_118; uint8 x_120; obj* x_123; obj* x_124; 
x_118 = lean::cnstr_get(x_109, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
lean::dec(x_109);
lean::inc(x_118);
if (lean::is_scalar(x_88)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_88;
}
lean::cnstr_set(x_123, 0, x_118);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_120);
x_124 = x_123;
x_76 = x_124;
x_77 = x_118;
x_78 = x_120;
goto lbl_79;
}
}
else
{
obj* x_126; uint8 x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_96);
x_126 = lean::cnstr_get(x_97, 0);
x_128 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_set(x_97, 0, lean::box(0));
 x_129 = x_97;
} else {
 lean::inc(x_126);
 lean::dec(x_97);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_130 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_130 = x_88;
}
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set_scalar(x_130, sizeof(void*)*1, x_128);
x_131 = x_130;
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_131);
if (lean::obj_tag(x_132) == 0)
{
obj* x_134; obj* x_136; obj* x_138; 
lean::dec(x_129);
x_134 = lean::cnstr_get(x_132, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_132, 1);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_132, 2);
lean::inc(x_138);
lean::dec(x_132);
x_84 = x_134;
x_85 = x_136;
x_86 = x_138;
goto lbl_87;
}
else
{
obj* x_141; uint8 x_143; obj* x_146; obj* x_147; 
x_141 = lean::cnstr_get(x_132, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get_scalar<uint8>(x_132, sizeof(void*)*1);
lean::dec(x_132);
lean::inc(x_141);
if (lean::is_scalar(x_129)) {
 x_146 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_146 = x_129;
}
lean::cnstr_set(x_146, 0, x_141);
lean::cnstr_set_scalar(x_146, sizeof(void*)*1, x_143);
x_147 = x_146;
x_76 = x_147;
x_77 = x_141;
x_78 = x_143;
goto lbl_79;
}
}
}
else
{
obj* x_148; uint8 x_150; obj* x_153; obj* x_154; 
x_148 = lean::cnstr_get(x_91, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
lean::dec(x_91);
lean::inc(x_148);
if (lean::is_scalar(x_88)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_88;
}
lean::cnstr_set(x_153, 0, x_148);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_150);
x_154 = x_153;
x_76 = x_154;
x_77 = x_148;
x_78 = x_150;
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
obj* x_157; obj* x_158; uint8 x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_165; obj* x_166; obj* x_167; 
if (x_78 == 0)
{
obj* x_170; obj* x_172; 
lean::dec(x_76);
x_170 = l_lean_ir_parse__instr___closed__1;
lean::inc(x_0);
x_172 = l_lean_ir_keyword(x_170, x_0);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_175; obj* x_177; obj* x_178; 
x_173 = lean::cnstr_get(x_172, 1);
x_175 = lean::cnstr_get(x_172, 2);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_set(x_172, 1, lean::box(0));
 lean::cnstr_set(x_172, 2, lean::box(0));
 x_177 = x_172;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_172);
 x_177 = lean::box(0);
}
x_178 = l_lean_ir_parse__var(x_173);
if (lean::obj_tag(x_178) == 0)
{
obj* x_179; obj* x_181; obj* x_183; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_178, 2);
lean::inc(x_183);
lean::dec(x_178);
x_186 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__2___boxed), 3, 1);
lean::closure_set(x_186, 0, x_179);
x_187 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_177)) {
 x_188 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_188 = x_177;
}
lean::cnstr_set(x_188, 0, x_186);
lean::cnstr_set(x_188, 1, x_181);
lean::cnstr_set(x_188, 2, x_187);
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_188);
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_189);
if (lean::obj_tag(x_190) == 0)
{
obj* x_191; obj* x_193; obj* x_195; 
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_190, 2);
lean::inc(x_195);
lean::dec(x_190);
x_165 = x_191;
x_166 = x_193;
x_167 = x_195;
goto lbl_168;
}
else
{
obj* x_198; uint8 x_200; obj* x_201; obj* x_203; obj* x_204; 
x_198 = lean::cnstr_get(x_190, 0);
x_200 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*1);
if (lean::is_exclusive(x_190)) {
 x_201 = x_190;
} else {
 lean::inc(x_198);
 lean::dec(x_190);
 x_201 = lean::box(0);
}
lean::inc(x_198);
if (lean::is_scalar(x_201)) {
 x_203 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_203 = x_201;
}
lean::cnstr_set(x_203, 0, x_198);
lean::cnstr_set_scalar(x_203, sizeof(void*)*1, x_200);
x_204 = x_203;
x_157 = x_204;
x_158 = x_198;
x_159 = x_200;
goto lbl_160;
}
}
else
{
obj* x_206; uint8 x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_177);
x_206 = lean::cnstr_get(x_178, 0);
x_208 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
if (lean::is_exclusive(x_178)) {
 x_209 = x_178;
} else {
 lean::inc(x_206);
 lean::dec(x_178);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_206);
lean::cnstr_set_scalar(x_210, sizeof(void*)*1, x_208);
x_211 = x_210;
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_211);
if (lean::obj_tag(x_212) == 0)
{
obj* x_213; obj* x_215; obj* x_217; 
x_213 = lean::cnstr_get(x_212, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_212, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 2);
lean::inc(x_217);
lean::dec(x_212);
x_165 = x_213;
x_166 = x_215;
x_167 = x_217;
goto lbl_168;
}
else
{
obj* x_220; uint8 x_222; obj* x_223; obj* x_225; obj* x_226; 
x_220 = lean::cnstr_get(x_212, 0);
x_222 = lean::cnstr_get_scalar<uint8>(x_212, sizeof(void*)*1);
if (lean::is_exclusive(x_212)) {
 x_223 = x_212;
} else {
 lean::inc(x_220);
 lean::dec(x_212);
 x_223 = lean::box(0);
}
lean::inc(x_220);
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_220);
lean::cnstr_set_scalar(x_225, sizeof(void*)*1, x_222);
x_226 = x_225;
x_157 = x_226;
x_158 = x_220;
x_159 = x_222;
goto lbl_160;
}
}
}
else
{
obj* x_227; uint8 x_229; obj* x_230; obj* x_232; obj* x_233; 
x_227 = lean::cnstr_get(x_172, 0);
x_229 = lean::cnstr_get_scalar<uint8>(x_172, sizeof(void*)*1);
if (lean::is_exclusive(x_172)) {
 x_230 = x_172;
} else {
 lean::inc(x_227);
 lean::dec(x_172);
 x_230 = lean::box(0);
}
lean::inc(x_227);
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_227);
lean::cnstr_set_scalar(x_232, sizeof(void*)*1, x_229);
x_233 = x_232;
x_157 = x_233;
x_158 = x_227;
x_159 = x_229;
goto lbl_160;
}
}
else
{
obj* x_236; 
lean::dec(x_77);
lean::dec(x_0);
x_236 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_76);
return x_236;
}
lbl_160:
{
obj* x_237; obj* x_238; obj* x_239; 
if (x_159 == 0)
{
obj* x_242; obj* x_243; obj* x_245; 
lean::dec(x_157);
x_242 = l_lean_ir_parse__typed__assignment___closed__5;
x_243 = l_lean_ir_str2unop;
lean::inc(x_0);
x_245 = l_lean_ir_parse__key2val___main___rarg(x_242, x_243, x_0);
if (lean::obj_tag(x_245) == 0)
{
obj* x_246; obj* x_248; obj* x_250; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
x_246 = lean::cnstr_get(x_245, 0);
x_248 = lean::cnstr_get(x_245, 1);
x_250 = lean::cnstr_get(x_245, 2);
if (lean::is_exclusive(x_245)) {
 x_252 = x_245;
} else {
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_245);
 x_252 = lean::box(0);
}
x_253 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__1___boxed), 2, 1);
lean::closure_set(x_253, 0, x_246);
x_254 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_252)) {
 x_255 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_255 = x_252;
}
lean::cnstr_set(x_255, 0, x_253);
lean::cnstr_set(x_255, 1, x_248);
lean::cnstr_set(x_255, 2, x_254);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_255);
if (lean::obj_tag(x_256) == 0)
{
obj* x_257; obj* x_259; obj* x_261; 
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_256, 1);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_256, 2);
lean::inc(x_261);
lean::dec(x_256);
x_237 = x_257;
x_238 = x_259;
x_239 = x_261;
goto lbl_240;
}
else
{
obj* x_264; uint8 x_266; obj* x_267; 
x_264 = lean::cnstr_get(x_256, 0);
x_266 = lean::cnstr_get_scalar<uint8>(x_256, sizeof(void*)*1);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_set(x_256, 0, lean::box(0));
 x_267 = x_256;
} else {
 lean::inc(x_264);
 lean::dec(x_256);
 x_267 = lean::box(0);
}
if (x_266 == 0)
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_267);
x_269 = l_lean_ir_parse__assignment(x_0);
x_270 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_264, x_269);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_270);
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_271);
x_273 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_272);
return x_273;
}
else
{
obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
lean::dec(x_0);
if (lean::is_scalar(x_267)) {
 x_275 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_275 = x_267;
}
lean::cnstr_set(x_275, 0, x_264);
lean::cnstr_set_scalar(x_275, sizeof(void*)*1, x_266);
x_276 = x_275;
x_277 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_276);
x_278 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_277);
x_279 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_278);
return x_279;
}
}
}
else
{
obj* x_280; uint8 x_282; obj* x_283; 
x_280 = lean::cnstr_get(x_245, 0);
x_282 = lean::cnstr_get_scalar<uint8>(x_245, sizeof(void*)*1);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_set(x_245, 0, lean::box(0));
 x_283 = x_245;
} else {
 lean::inc(x_280);
 lean::dec(x_245);
 x_283 = lean::box(0);
}
if (x_282 == 0)
{
obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_283);
x_285 = l_lean_ir_parse__assignment(x_0);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_280, x_285);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_286);
x_288 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_287);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_288);
return x_289;
}
else
{
obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_0);
if (lean::is_scalar(x_283)) {
 x_291 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_291 = x_283;
}
lean::cnstr_set(x_291, 0, x_280);
lean::cnstr_set_scalar(x_291, sizeof(void*)*1, x_282);
x_292 = x_291;
x_293 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_292);
x_294 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_293);
x_295 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_294);
return x_295;
}
}
}
else
{
obj* x_298; obj* x_299; 
lean::dec(x_0);
lean::dec(x_158);
x_298 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_157);
x_299 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_298);
return x_299;
}
lbl_240:
{
obj* x_300; 
x_300 = l_lean_ir_parse__var(x_238);
if (lean::obj_tag(x_300) == 0)
{
obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_301 = lean::cnstr_get(x_300, 0);
x_303 = lean::cnstr_get(x_300, 1);
x_305 = lean::cnstr_get(x_300, 2);
if (lean::is_exclusive(x_300)) {
 x_307 = x_300;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::dec(x_300);
 x_307 = lean::box(0);
}
x_308 = lean::apply_1(x_237, x_301);
x_309 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_307)) {
 x_310 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_310 = x_307;
}
lean::cnstr_set(x_310, 0, x_308);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_309);
x_311 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_305, x_310);
x_312 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_311);
if (lean::obj_tag(x_312) == 0)
{
obj* x_314; obj* x_315; obj* x_316; 
lean::dec(x_0);
x_314 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_312);
x_315 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_314);
x_316 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_315);
return x_316;
}
else
{
obj* x_317; uint8 x_319; 
x_317 = lean::cnstr_get(x_312, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get_scalar<uint8>(x_312, sizeof(void*)*1);
if (x_319 == 0)
{
obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_312);
x_321 = l_lean_ir_parse__assignment(x_0);
x_322 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_317, x_321);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_322);
x_324 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_323);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_324);
return x_325;
}
else
{
obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_0);
lean::dec(x_317);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_312);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_328);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_329);
return x_330;
}
}
}
else
{
obj* x_332; uint8 x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; 
lean::dec(x_237);
x_332 = lean::cnstr_get(x_300, 0);
x_334 = lean::cnstr_get_scalar<uint8>(x_300, sizeof(void*)*1);
if (lean::is_exclusive(x_300)) {
 x_335 = x_300;
} else {
 lean::inc(x_332);
 lean::dec(x_300);
 x_335 = lean::box(0);
}
if (lean::is_scalar(x_335)) {
 x_336 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_336 = x_335;
}
lean::cnstr_set(x_336, 0, x_332);
lean::cnstr_set_scalar(x_336, sizeof(void*)*1, x_334);
x_337 = x_336;
x_338 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_337);
if (lean::obj_tag(x_338) == 0)
{
obj* x_340; obj* x_341; obj* x_342; 
lean::dec(x_0);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_338);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_340);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_341);
return x_342;
}
else
{
obj* x_343; uint8 x_345; 
x_343 = lean::cnstr_get(x_338, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get_scalar<uint8>(x_338, sizeof(void*)*1);
if (x_345 == 0)
{
obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
lean::dec(x_338);
x_347 = l_lean_ir_parse__assignment(x_0);
x_348 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_343, x_347);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_348);
x_350 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_349);
x_351 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_350);
return x_351;
}
else
{
obj* x_354; obj* x_355; obj* x_356; 
lean::dec(x_0);
lean::dec(x_343);
x_354 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_158, x_338);
x_355 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_354);
x_356 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_355);
return x_356;
}
}
}
}
}
lbl_164:
{
obj* x_357; 
x_357 = l_lean_ir_parse__var(x_162);
if (lean::obj_tag(x_357) == 0)
{
obj* x_358; obj* x_360; obj* x_362; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; 
x_358 = lean::cnstr_get(x_357, 0);
x_360 = lean::cnstr_get(x_357, 1);
x_362 = lean::cnstr_get(x_357, 2);
if (lean::is_exclusive(x_357)) {
 x_364 = x_357;
} else {
 lean::inc(x_358);
 lean::inc(x_360);
 lean::inc(x_362);
 lean::dec(x_357);
 x_364 = lean::box(0);
}
x_365 = lean::apply_1(x_161, x_358);
x_366 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_364)) {
 x_367 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_367 = x_364;
}
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_366);
x_368 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_362, x_367);
x_369 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_368);
if (lean::obj_tag(x_369) == 0)
{
obj* x_371; obj* x_372; 
lean::dec(x_0);
x_371 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_369);
x_372 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_371);
return x_372;
}
else
{
obj* x_373; uint8 x_375; 
x_373 = lean::cnstr_get(x_369, 0);
lean::inc(x_373);
x_375 = lean::cnstr_get_scalar<uint8>(x_369, sizeof(void*)*1);
x_157 = x_369;
x_158 = x_373;
x_159 = x_375;
goto lbl_160;
}
}
else
{
obj* x_377; uint8 x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; 
lean::dec(x_161);
x_377 = lean::cnstr_get(x_357, 0);
x_379 = lean::cnstr_get_scalar<uint8>(x_357, sizeof(void*)*1);
if (lean::is_exclusive(x_357)) {
 x_380 = x_357;
} else {
 lean::inc(x_377);
 lean::dec(x_357);
 x_380 = lean::box(0);
}
if (lean::is_scalar(x_380)) {
 x_381 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_381 = x_380;
}
lean::cnstr_set(x_381, 0, x_377);
lean::cnstr_set_scalar(x_381, sizeof(void*)*1, x_379);
x_382 = x_381;
x_383 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_382);
if (lean::obj_tag(x_383) == 0)
{
obj* x_385; obj* x_386; 
lean::dec(x_0);
x_385 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_383);
x_386 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_385);
return x_386;
}
else
{
obj* x_387; uint8 x_389; 
x_387 = lean::cnstr_get(x_383, 0);
lean::inc(x_387);
x_389 = lean::cnstr_get_scalar<uint8>(x_383, sizeof(void*)*1);
x_157 = x_383;
x_158 = x_387;
x_159 = x_389;
goto lbl_160;
}
}
}
lbl_168:
{
obj* x_390; 
x_390 = l_lean_ir_parse__usize(x_166);
if (lean::obj_tag(x_390) == 0)
{
obj* x_391; obj* x_393; obj* x_395; obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; 
x_391 = lean::cnstr_get(x_390, 0);
x_393 = lean::cnstr_get(x_390, 1);
x_395 = lean::cnstr_get(x_390, 2);
if (lean::is_exclusive(x_390)) {
 x_397 = x_390;
} else {
 lean::inc(x_391);
 lean::inc(x_393);
 lean::inc(x_395);
 lean::dec(x_390);
 x_397 = lean::box(0);
}
x_398 = lean::apply_1(x_165, x_391);
x_399 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_397)) {
 x_400 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_400 = x_397;
}
lean::cnstr_set(x_400, 0, x_398);
lean::cnstr_set(x_400, 1, x_393);
lean::cnstr_set(x_400, 2, x_399);
x_401 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_395, x_400);
x_402 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_401);
if (lean::obj_tag(x_402) == 0)
{
obj* x_403; obj* x_405; obj* x_407; 
x_403 = lean::cnstr_get(x_402, 0);
lean::inc(x_403);
x_405 = lean::cnstr_get(x_402, 1);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_402, 2);
lean::inc(x_407);
lean::dec(x_402);
x_161 = x_403;
x_162 = x_405;
x_163 = x_407;
goto lbl_164;
}
else
{
obj* x_410; uint8 x_412; obj* x_413; obj* x_415; obj* x_416; 
x_410 = lean::cnstr_get(x_402, 0);
x_412 = lean::cnstr_get_scalar<uint8>(x_402, sizeof(void*)*1);
if (lean::is_exclusive(x_402)) {
 x_413 = x_402;
} else {
 lean::inc(x_410);
 lean::dec(x_402);
 x_413 = lean::box(0);
}
lean::inc(x_410);
if (lean::is_scalar(x_413)) {
 x_415 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_415 = x_413;
}
lean::cnstr_set(x_415, 0, x_410);
lean::cnstr_set_scalar(x_415, sizeof(void*)*1, x_412);
x_416 = x_415;
x_157 = x_416;
x_158 = x_410;
x_159 = x_412;
goto lbl_160;
}
}
else
{
obj* x_418; uint8 x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
lean::dec(x_165);
x_418 = lean::cnstr_get(x_390, 0);
x_420 = lean::cnstr_get_scalar<uint8>(x_390, sizeof(void*)*1);
if (lean::is_exclusive(x_390)) {
 x_421 = x_390;
} else {
 lean::inc(x_418);
 lean::dec(x_390);
 x_421 = lean::box(0);
}
if (lean::is_scalar(x_421)) {
 x_422 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_422 = x_421;
}
lean::cnstr_set(x_422, 0, x_418);
lean::cnstr_set_scalar(x_422, sizeof(void*)*1, x_420);
x_423 = x_422;
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_423);
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
x_161 = x_425;
x_162 = x_427;
x_163 = x_429;
goto lbl_164;
}
else
{
obj* x_432; uint8 x_434; obj* x_435; obj* x_437; obj* x_438; 
x_432 = lean::cnstr_get(x_424, 0);
x_434 = lean::cnstr_get_scalar<uint8>(x_424, sizeof(void*)*1);
if (lean::is_exclusive(x_424)) {
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
x_157 = x_438;
x_158 = x_432;
x_159 = x_434;
goto lbl_160;
}
}
}
}
lbl_83:
{
obj* x_439; 
x_439 = l_lean_ir_parse__var(x_81);
if (lean::obj_tag(x_439) == 0)
{
obj* x_440; obj* x_442; obj* x_444; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; 
x_440 = lean::cnstr_get(x_439, 0);
x_442 = lean::cnstr_get(x_439, 1);
x_444 = lean::cnstr_get(x_439, 2);
if (lean::is_exclusive(x_439)) {
 x_446 = x_439;
} else {
 lean::inc(x_440);
 lean::inc(x_442);
 lean::inc(x_444);
 lean::dec(x_439);
 x_446 = lean::box(0);
}
x_447 = lean::apply_1(x_80, x_440);
x_448 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_446)) {
 x_449 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_449 = x_446;
}
lean::cnstr_set(x_449, 0, x_447);
lean::cnstr_set(x_449, 1, x_442);
lean::cnstr_set(x_449, 2, x_448);
x_450 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_444, x_449);
x_451 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_450);
if (lean::obj_tag(x_451) == 0)
{
obj* x_453; 
lean::dec(x_0);
x_453 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_451);
return x_453;
}
else
{
obj* x_454; uint8 x_456; 
x_454 = lean::cnstr_get(x_451, 0);
lean::inc(x_454);
x_456 = lean::cnstr_get_scalar<uint8>(x_451, sizeof(void*)*1);
x_76 = x_451;
x_77 = x_454;
x_78 = x_456;
goto lbl_79;
}
}
else
{
obj* x_458; uint8 x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
lean::dec(x_80);
x_458 = lean::cnstr_get(x_439, 0);
x_460 = lean::cnstr_get_scalar<uint8>(x_439, sizeof(void*)*1);
if (lean::is_exclusive(x_439)) {
 x_461 = x_439;
} else {
 lean::inc(x_458);
 lean::dec(x_439);
 x_461 = lean::box(0);
}
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_458);
lean::cnstr_set_scalar(x_462, sizeof(void*)*1, x_460);
x_463 = x_462;
x_464 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_463);
if (lean::obj_tag(x_464) == 0)
{
obj* x_466; 
lean::dec(x_0);
x_466 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_464);
return x_466;
}
else
{
obj* x_467; uint8 x_469; 
x_467 = lean::cnstr_get(x_464, 0);
lean::inc(x_467);
x_469 = lean::cnstr_get_scalar<uint8>(x_464, sizeof(void*)*1);
x_76 = x_464;
x_77 = x_467;
x_78 = x_469;
goto lbl_79;
}
}
}
lbl_87:
{
obj* x_470; 
x_470 = l_lean_ir_parse__uint16(x_85);
if (lean::obj_tag(x_470) == 0)
{
obj* x_471; obj* x_473; obj* x_475; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; 
x_471 = lean::cnstr_get(x_470, 0);
x_473 = lean::cnstr_get(x_470, 1);
x_475 = lean::cnstr_get(x_470, 2);
if (lean::is_exclusive(x_470)) {
 x_477 = x_470;
} else {
 lean::inc(x_471);
 lean::inc(x_473);
 lean::inc(x_475);
 lean::dec(x_470);
 x_477 = lean::box(0);
}
x_478 = lean::apply_1(x_84, x_471);
x_479 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_477)) {
 x_480 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_480 = x_477;
}
lean::cnstr_set(x_480, 0, x_478);
lean::cnstr_set(x_480, 1, x_473);
lean::cnstr_set(x_480, 2, x_479);
x_481 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_475, x_480);
x_482 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_481);
if (lean::obj_tag(x_482) == 0)
{
obj* x_483; obj* x_485; obj* x_487; 
x_483 = lean::cnstr_get(x_482, 0);
lean::inc(x_483);
x_485 = lean::cnstr_get(x_482, 1);
lean::inc(x_485);
x_487 = lean::cnstr_get(x_482, 2);
lean::inc(x_487);
lean::dec(x_482);
x_80 = x_483;
x_81 = x_485;
x_82 = x_487;
goto lbl_83;
}
else
{
obj* x_490; uint8 x_492; obj* x_493; obj* x_495; obj* x_496; 
x_490 = lean::cnstr_get(x_482, 0);
x_492 = lean::cnstr_get_scalar<uint8>(x_482, sizeof(void*)*1);
if (lean::is_exclusive(x_482)) {
 x_493 = x_482;
} else {
 lean::inc(x_490);
 lean::dec(x_482);
 x_493 = lean::box(0);
}
lean::inc(x_490);
if (lean::is_scalar(x_493)) {
 x_495 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_495 = x_493;
}
lean::cnstr_set(x_495, 0, x_490);
lean::cnstr_set_scalar(x_495, sizeof(void*)*1, x_492);
x_496 = x_495;
x_76 = x_496;
x_77 = x_490;
x_78 = x_492;
goto lbl_79;
}
}
else
{
obj* x_498; uint8 x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; 
lean::dec(x_84);
x_498 = lean::cnstr_get(x_470, 0);
x_500 = lean::cnstr_get_scalar<uint8>(x_470, sizeof(void*)*1);
if (lean::is_exclusive(x_470)) {
 x_501 = x_470;
} else {
 lean::inc(x_498);
 lean::dec(x_470);
 x_501 = lean::box(0);
}
if (lean::is_scalar(x_501)) {
 x_502 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_502 = x_501;
}
lean::cnstr_set(x_502, 0, x_498);
lean::cnstr_set_scalar(x_502, sizeof(void*)*1, x_500);
x_503 = x_502;
x_504 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_503);
if (lean::obj_tag(x_504) == 0)
{
obj* x_505; obj* x_507; obj* x_509; 
x_505 = lean::cnstr_get(x_504, 0);
lean::inc(x_505);
x_507 = lean::cnstr_get(x_504, 1);
lean::inc(x_507);
x_509 = lean::cnstr_get(x_504, 2);
lean::inc(x_509);
lean::dec(x_504);
x_80 = x_505;
x_81 = x_507;
x_82 = x_509;
goto lbl_83;
}
else
{
obj* x_512; uint8 x_514; obj* x_515; obj* x_517; obj* x_518; 
x_512 = lean::cnstr_get(x_504, 0);
x_514 = lean::cnstr_get_scalar<uint8>(x_504, sizeof(void*)*1);
if (lean::is_exclusive(x_504)) {
 x_515 = x_504;
} else {
 lean::inc(x_512);
 lean::dec(x_504);
 x_515 = lean::box(0);
}
lean::inc(x_512);
if (lean::is_scalar(x_515)) {
 x_517 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_517 = x_515;
}
lean::cnstr_set(x_517, 0, x_512);
lean::cnstr_set_scalar(x_517, sizeof(void*)*1, x_514);
x_518 = x_517;
x_76 = x_518;
x_77 = x_512;
x_78 = x_514;
goto lbl_79;
}
}
}
}
}
lbl_6:
{
obj* x_519; 
x_519 = l_lean_ir_parse__var(x_4);
if (lean::obj_tag(x_519) == 0)
{
obj* x_520; obj* x_522; obj* x_524; obj* x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; obj* x_531; 
x_520 = lean::cnstr_get(x_519, 0);
x_522 = lean::cnstr_get(x_519, 1);
x_524 = lean::cnstr_get(x_519, 2);
if (lean::is_exclusive(x_519)) {
 x_526 = x_519;
} else {
 lean::inc(x_520);
 lean::inc(x_522);
 lean::inc(x_524);
 lean::dec(x_519);
 x_526 = lean::box(0);
}
x_527 = lean::apply_1(x_3, x_520);
x_528 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_526)) {
 x_529 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_529 = x_526;
}
lean::cnstr_set(x_529, 0, x_527);
lean::cnstr_set(x_529, 1, x_522);
lean::cnstr_set(x_529, 2, x_528);
x_530 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_524, x_529);
x_531 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_530);
x_1 = x_531;
goto lbl_2;
}
else
{
obj* x_533; uint8 x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; 
lean::dec(x_3);
x_533 = lean::cnstr_get(x_519, 0);
x_535 = lean::cnstr_get_scalar<uint8>(x_519, sizeof(void*)*1);
if (lean::is_exclusive(x_519)) {
 x_536 = x_519;
} else {
 lean::inc(x_533);
 lean::dec(x_519);
 x_536 = lean::box(0);
}
if (lean::is_scalar(x_536)) {
 x_537 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_537 = x_536;
}
lean::cnstr_set(x_537, 0, x_533);
lean::cnstr_set_scalar(x_537, sizeof(void*)*1, x_535);
x_538 = x_537;
x_539 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_538);
x_1 = x_539;
goto lbl_2;
}
}
lbl_10:
{
obj* x_540; 
x_540 = l_lean_ir_parse__var(x_8);
if (lean::obj_tag(x_540) == 0)
{
obj* x_541; obj* x_543; obj* x_545; obj* x_547; obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; 
x_541 = lean::cnstr_get(x_540, 0);
x_543 = lean::cnstr_get(x_540, 1);
x_545 = lean::cnstr_get(x_540, 2);
if (lean::is_exclusive(x_540)) {
 x_547 = x_540;
} else {
 lean::inc(x_541);
 lean::inc(x_543);
 lean::inc(x_545);
 lean::dec(x_540);
 x_547 = lean::box(0);
}
x_548 = lean::apply_1(x_7, x_541);
x_549 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_547)) {
 x_550 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_550 = x_547;
}
lean::cnstr_set(x_550, 0, x_548);
lean::cnstr_set(x_550, 1, x_543);
lean::cnstr_set(x_550, 2, x_549);
x_551 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_545, x_550);
x_552 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_551);
if (lean::obj_tag(x_552) == 0)
{
obj* x_553; obj* x_555; obj* x_557; 
x_553 = lean::cnstr_get(x_552, 0);
lean::inc(x_553);
x_555 = lean::cnstr_get(x_552, 1);
lean::inc(x_555);
x_557 = lean::cnstr_get(x_552, 2);
lean::inc(x_557);
lean::dec(x_552);
x_3 = x_553;
x_4 = x_555;
x_5 = x_557;
goto lbl_6;
}
else
{
obj* x_560; uint8 x_562; obj* x_563; obj* x_564; obj* x_565; 
x_560 = lean::cnstr_get(x_552, 0);
x_562 = lean::cnstr_get_scalar<uint8>(x_552, sizeof(void*)*1);
if (lean::is_exclusive(x_552)) {
 x_563 = x_552;
} else {
 lean::inc(x_560);
 lean::dec(x_552);
 x_563 = lean::box(0);
}
if (lean::is_scalar(x_563)) {
 x_564 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_564 = x_563;
}
lean::cnstr_set(x_564, 0, x_560);
lean::cnstr_set_scalar(x_564, sizeof(void*)*1, x_562);
x_565 = x_564;
x_1 = x_565;
goto lbl_2;
}
}
else
{
obj* x_567; uint8 x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; 
lean::dec(x_7);
x_567 = lean::cnstr_get(x_540, 0);
x_569 = lean::cnstr_get_scalar<uint8>(x_540, sizeof(void*)*1);
if (lean::is_exclusive(x_540)) {
 x_570 = x_540;
} else {
 lean::inc(x_567);
 lean::dec(x_540);
 x_570 = lean::box(0);
}
if (lean::is_scalar(x_570)) {
 x_571 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_571 = x_570;
}
lean::cnstr_set(x_571, 0, x_567);
lean::cnstr_set_scalar(x_571, sizeof(void*)*1, x_569);
x_572 = x_571;
x_573 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_572);
if (lean::obj_tag(x_573) == 0)
{
obj* x_574; obj* x_576; obj* x_578; 
x_574 = lean::cnstr_get(x_573, 0);
lean::inc(x_574);
x_576 = lean::cnstr_get(x_573, 1);
lean::inc(x_576);
x_578 = lean::cnstr_get(x_573, 2);
lean::inc(x_578);
lean::dec(x_573);
x_3 = x_574;
x_4 = x_576;
x_5 = x_578;
goto lbl_6;
}
else
{
obj* x_581; uint8 x_583; obj* x_584; obj* x_585; obj* x_586; 
x_581 = lean::cnstr_get(x_573, 0);
x_583 = lean::cnstr_get_scalar<uint8>(x_573, sizeof(void*)*1);
if (lean::is_exclusive(x_573)) {
 x_584 = x_573;
} else {
 lean::inc(x_581);
 lean::dec(x_573);
 x_584 = lean::box(0);
}
if (lean::is_scalar(x_584)) {
 x_585 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_585 = x_584;
}
lean::cnstr_set(x_585, 0, x_581);
lean::cnstr_set_scalar(x_585, sizeof(void*)*1, x_583);
x_586 = x_585;
x_1 = x_586;
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
obj* x_46; obj* x_47; obj* x_49; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_46 = x_1;
} else {
 lean::dec(x_1);
 x_46 = lean::box(0);
}
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
obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_46);
x_57 = lean::cnstr_get(x_55, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_55, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_55, 2);
lean::inc(x_61);
lean::dec(x_55);
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_57);
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_54)) {
 x_66 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_66 = x_54;
}
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_59);
lean::cnstr_set(x_66, 2, x_65);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_66);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; 
lean::dec(x_0);
x_70 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_68);
return x_70;
}
else
{
obj* x_71; uint8 x_73; 
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
x_42 = x_68;
x_43 = x_71;
x_44 = x_73;
goto lbl_45;
}
}
else
{
obj* x_75; uint8 x_77; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_54);
x_75 = lean::cnstr_get(x_55, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
lean::dec(x_55);
if (lean::is_scalar(x_46)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_46;
}
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = x_79;
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_83; 
lean::dec(x_0);
x_83 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_81);
return x_83;
}
else
{
obj* x_84; uint8 x_86; 
x_84 = lean::cnstr_get(x_81, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get_scalar<uint8>(x_81, sizeof(void*)*1);
x_42 = x_81;
x_43 = x_84;
x_44 = x_86;
goto lbl_45;
}
}
}
else
{
obj* x_87; uint8 x_89; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_49, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
lean::dec(x_49);
lean::inc(x_87);
if (lean::is_scalar(x_46)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_46;
}
lean::cnstr_set(x_92, 0, x_87);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_89);
x_93 = x_92;
x_42 = x_93;
x_43 = x_87;
x_44 = x_89;
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
obj* x_96; obj* x_97; obj* x_98; 
if (x_44 == 0)
{
obj* x_101; obj* x_102; 
lean::dec(x_42);
x_101 = l_lean_ir_parse__terminator___closed__1;
x_102 = l_lean_ir_keyword(x_101, x_0);
if (lean::obj_tag(x_102) == 0)
{
obj* x_103; obj* x_105; obj* x_107; obj* x_108; 
x_103 = lean::cnstr_get(x_102, 1);
x_105 = lean::cnstr_get(x_102, 2);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_set(x_102, 1, lean::box(0));
 lean::cnstr_set(x_102, 2, lean::box(0));
 x_107 = x_102;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_102);
 x_107 = lean::box(0);
}
x_108 = l_lean_ir_parse__var(x_103);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_111; obj* x_113; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_108, 2);
lean::inc(x_113);
lean::dec(x_108);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__terminator___lambda__1), 2, 1);
lean::closure_set(x_116, 0, x_109);
x_117 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_107)) {
 x_118 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_118 = x_107;
}
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_111);
lean::cnstr_set(x_118, 2, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_118);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_123; obj* x_125; 
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_120, 2);
lean::inc(x_125);
lean::dec(x_120);
x_96 = x_121;
x_97 = x_123;
x_98 = x_125;
goto lbl_99;
}
else
{
obj* x_128; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_128 = lean::cnstr_get(x_120, 0);
x_130 = lean::cnstr_get_scalar<uint8>(x_120, sizeof(void*)*1);
if (lean::is_exclusive(x_120)) {
 x_131 = x_120;
} else {
 lean::inc(x_128);
 lean::dec(x_120);
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
x_134 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_133);
x_135 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_134);
return x_135;
}
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_107);
x_137 = lean::cnstr_get(x_108, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_108, sizeof(void*)*1);
if (lean::is_exclusive(x_108)) {
 x_140 = x_108;
} else {
 lean::inc(x_137);
 lean::dec(x_108);
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
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_142);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_146; obj* x_148; 
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_143, 2);
lean::inc(x_148);
lean::dec(x_143);
x_96 = x_144;
x_97 = x_146;
x_98 = x_148;
goto lbl_99;
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_151 = lean::cnstr_get(x_143, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_143, sizeof(void*)*1);
if (lean::is_exclusive(x_143)) {
 x_154 = x_143;
} else {
 lean::inc(x_151);
 lean::dec(x_143);
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
x_157 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_156);
x_158 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_157);
return x_158;
}
}
}
else
{
obj* x_159; uint8 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_159 = lean::cnstr_get(x_102, 0);
x_161 = lean::cnstr_get_scalar<uint8>(x_102, sizeof(void*)*1);
if (lean::is_exclusive(x_102)) {
 x_162 = x_102;
} else {
 lean::inc(x_159);
 lean::dec(x_102);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_159);
lean::cnstr_set_scalar(x_163, sizeof(void*)*1, x_161);
x_164 = x_163;
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_164);
x_166 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_165);
return x_166;
}
}
else
{
obj* x_169; 
lean::dec(x_43);
lean::dec(x_0);
x_169 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_42);
return x_169;
}
lbl_99:
{
obj* x_170; obj* x_171; obj* x_172; obj* x_174; obj* x_175; 
x_174 = l_list_repr___main___rarg___closed__2;
x_175 = l_lean_ir_symbol(x_174, x_97);
if (lean::obj_tag(x_175) == 0)
{
obj* x_176; obj* x_178; obj* x_181; obj* x_182; 
x_176 = lean::cnstr_get(x_175, 1);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_175, 2);
lean::inc(x_178);
lean::dec(x_175);
x_181 = l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(x_176);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_181);
if (lean::obj_tag(x_182) == 0)
{
obj* x_183; obj* x_185; obj* x_187; 
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_182, 1);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_182, 2);
lean::inc(x_187);
lean::dec(x_182);
x_170 = x_183;
x_171 = x_185;
x_172 = x_187;
goto lbl_173;
}
else
{
obj* x_191; uint8 x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_96);
x_191 = lean::cnstr_get(x_182, 0);
x_193 = lean::cnstr_get_scalar<uint8>(x_182, sizeof(void*)*1);
if (lean::is_exclusive(x_182)) {
 x_194 = x_182;
} else {
 lean::inc(x_191);
 lean::dec(x_182);
 x_194 = lean::box(0);
}
if (lean::is_scalar(x_194)) {
 x_195 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_195 = x_194;
}
lean::cnstr_set(x_195, 0, x_191);
lean::cnstr_set_scalar(x_195, sizeof(void*)*1, x_193);
x_196 = x_195;
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_196);
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_198);
return x_199;
}
}
else
{
obj* x_201; uint8 x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_96);
x_201 = lean::cnstr_get(x_175, 0);
x_203 = lean::cnstr_get_scalar<uint8>(x_175, sizeof(void*)*1);
if (lean::is_exclusive(x_175)) {
 x_204 = x_175;
} else {
 lean::inc(x_201);
 lean::dec(x_175);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_201);
lean::cnstr_set_scalar(x_205, sizeof(void*)*1, x_203);
x_206 = x_205;
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_206);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_207);
x_209 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_208);
return x_209;
}
lbl_173:
{
obj* x_210; obj* x_211; 
x_210 = l_list_repr___main___rarg___closed__3;
x_211 = l_lean_ir_symbol(x_210, x_171);
if (lean::obj_tag(x_211) == 0)
{
obj* x_212; obj* x_214; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_212 = lean::cnstr_get(x_211, 1);
x_214 = lean::cnstr_get(x_211, 2);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_216 = x_211;
} else {
 lean::inc(x_212);
 lean::inc(x_214);
 lean::dec(x_211);
 x_216 = lean::box(0);
}
x_217 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_216)) {
 x_218 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_218 = x_216;
}
lean::cnstr_set(x_218, 0, x_170);
lean::cnstr_set(x_218, 1, x_212);
lean::cnstr_set(x_218, 2, x_217);
x_219 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_218);
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_172, x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_221; obj* x_223; obj* x_225; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_221 = lean::cnstr_get(x_220, 0);
x_223 = lean::cnstr_get(x_220, 1);
x_225 = lean::cnstr_get(x_220, 2);
if (lean::is_exclusive(x_220)) {
 x_227 = x_220;
} else {
 lean::inc(x_221);
 lean::inc(x_223);
 lean::inc(x_225);
 lean::dec(x_220);
 x_227 = lean::box(0);
}
x_228 = lean::apply_1(x_96, x_221);
if (lean::is_scalar(x_227)) {
 x_229 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_229 = x_227;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_223);
lean::cnstr_set(x_229, 2, x_217);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_225, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_231);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_232);
return x_233;
}
else
{
obj* x_235; uint8 x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
lean::dec(x_96);
x_235 = lean::cnstr_get(x_220, 0);
x_237 = lean::cnstr_get_scalar<uint8>(x_220, sizeof(void*)*1);
if (lean::is_exclusive(x_220)) {
 x_238 = x_220;
} else {
 lean::inc(x_235);
 lean::dec(x_220);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_235);
lean::cnstr_set_scalar(x_239, sizeof(void*)*1, x_237);
x_240 = x_239;
x_241 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_240);
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_241);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_242);
return x_243;
}
}
else
{
obj* x_245; uint8 x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_170);
x_245 = lean::cnstr_get(x_211, 0);
x_247 = lean::cnstr_get_scalar<uint8>(x_211, sizeof(void*)*1);
if (lean::is_exclusive(x_211)) {
 x_248 = x_211;
} else {
 lean::inc(x_245);
 lean::dec(x_211);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_245);
lean::cnstr_set_scalar(x_249, sizeof(void*)*1, x_247);
x_250 = x_249;
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_172, x_250);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_254; obj* x_256; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
x_252 = lean::cnstr_get(x_251, 0);
x_254 = lean::cnstr_get(x_251, 1);
x_256 = lean::cnstr_get(x_251, 2);
if (lean::is_exclusive(x_251)) {
 x_258 = x_251;
} else {
 lean::inc(x_252);
 lean::inc(x_254);
 lean::inc(x_256);
 lean::dec(x_251);
 x_258 = lean::box(0);
}
x_259 = lean::apply_1(x_96, x_252);
x_260 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_258)) {
 x_261 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_261 = x_258;
}
lean::cnstr_set(x_261, 0, x_259);
lean::cnstr_set(x_261, 1, x_254);
lean::cnstr_set(x_261, 2, x_260);
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_256, x_261);
x_263 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_262);
x_264 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_263);
x_265 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_264);
return x_265;
}
else
{
obj* x_267; uint8 x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_96);
x_267 = lean::cnstr_get(x_251, 0);
x_269 = lean::cnstr_get_scalar<uint8>(x_251, sizeof(void*)*1);
if (lean::is_exclusive(x_251)) {
 x_270 = x_251;
} else {
 lean::inc(x_267);
 lean::dec(x_251);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_267);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_269);
x_272 = x_271;
x_273 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_272);
x_274 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_273);
x_275 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_274);
return x_275;
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
