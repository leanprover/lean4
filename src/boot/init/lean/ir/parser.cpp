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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(uint32, obj*);
obj* l_lean_ir_parse__untyped__assignment(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat2int(obj*);
}
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__arg(obj*);
uint8 l_char_is__whitespace(uint32);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9___boxed(obj*, obj*);
obj* l_lean_ir_str2abinop;
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(obj*, obj*);
extern uint8 l_true_decidable;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2___boxed(obj*, obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_ir_identifier(obj*);
obj* l_lean_ir_identifier___closed__1;
obj* l_lean_ir_parse__instr___closed__2;
obj* l_lean_ir_parse__literal___closed__2;
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg___boxed(obj*, obj*, obj*);
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
obj* l_lean_ir_parse__key2val___main___boxed(obj*);
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
obj* l_id___rarg___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3___boxed(obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3___boxed(obj*, obj*);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(obj*, obj*, obj*);
obj* l_string_to__nat(obj*);
obj* l_lean_ir_parse__key2val___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20___boxed(obj*, obj*, obj*);
obj* l_lean_ir_parse__literal___closed__3;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__header___spec__2(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_ir_parse__literal___spec__5(obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__14(obj*, obj*, obj*);
obj* l_lean_ir_parse__block(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_ir_parse__var(obj*);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15___boxed(obj*, obj*);
obj* l_lean_ir_parse__instr___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_sep__by1___rarg___lambda__1(obj*, obj*);
obj* l_lean_ir_parse__def___lambda__1(obj*, obj*);
obj* l_lean_ir_parse__blockid___closed__1;
obj* l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3___boxed(obj*, obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__3(obj*, uint8, obj*, usize);
extern obj* l_bool_has__repr___closed__2;
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_identifier___spec__12(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__10(obj*, obj*, obj*);
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_lean_ir_parse__usize___closed__1;
uint8 l_lean_ir_is__reserved__name___main(obj*);
obj* l_lean_ir_str2aunop;
obj* l_lean_parser_monad__parsec_digit___at_lean_ir_parse__literal___spec__8(obj*);
obj* l_lean_parser_id__part___at_lean_ir_identifier___spec__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___boxed(obj*, obj*);
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
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
obj* l_lean_ir_keyword(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(uint32, obj*);
extern obj* l_uint16__sz;
obj* l_lean_ir_parse__typed__assignment___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___boxed(obj*, obj*);
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
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_10 = lean::box(0);
x_11 = l_string_join___closed__1;
x_12 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_12, 2, x_1);
lean::cnstr_set(x_12, 3, x_10);
x_13 = 0;
x_14 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1, x_13);
x_15 = x_14;
return x_15;
}
else
{
obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_1);
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
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_0);
x_25 = l_string_join___closed__1;
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_2);
lean::cnstr_set(x_27, 2, x_26);
return x_27;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_lean_ir_keyword___closed__1() {
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
obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_14);
x_73 = l_char_quote__core(x_43);
x_74 = lean::string_append(x_5, x_73);
lean::dec(x_73);
x_76 = lean::string_append(x_74, x_5);
x_77 = lean::box(0);
x_78 = l_mjoin___rarg___closed__1;
x_79 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_76, x_78, x_77, x_77, x_10);
lean::dec(x_10);
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_79);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_84);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_89);
x_91 = l_lean_parser_parsec__t_try__mk__res___rarg(x_90);
x_92 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_91, x_8);
return x_92;
}
else
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_103; uint8 x_104; obj* x_105; obj* x_106; 
x_93 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_95 = x_83;
} else {
 lean::inc(x_93);
 lean::dec(x_83);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_93, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_93, 3);
lean::inc(x_100);
lean::dec(x_93);
x_103 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_103, 0, x_96);
lean::cnstr_set(x_103, 1, x_98);
lean::cnstr_set(x_103, 2, x_8);
lean::cnstr_set(x_103, 3, x_100);
x_104 = 0;
if (lean::is_scalar(x_95)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_95;
}
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_104);
x_106 = x_105;
return x_106;
}
}
}
}
else
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_107 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_109 = x_9;
} else {
 lean::inc(x_107);
 lean::dec(x_9);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_107, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_107, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_107, 3);
lean::inc(x_114);
lean::dec(x_107);
x_117 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_117, 0, x_110);
lean::cnstr_set(x_117, 1, x_112);
lean::cnstr_set(x_117, 2, x_8);
lean::cnstr_set(x_117, 3, x_114);
x_118 = 0;
if (lean::is_scalar(x_109)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_109;
}
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_118);
x_120 = x_119;
return x_120;
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
lean::dec(x_2);
return x_5;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_2);
x_18 = l_lean_ir_keyword(x_12, x_2);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_18, 1);
x_21 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_23 = x_18;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_18);
 x_23 = lean::box(0);
}
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_19);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_25);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_0);
lean::dec(x_9);
lean::dec(x_2);
return x_26;
}
else
{
obj* x_30; uint8 x_32; 
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_32 == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_26);
x_34 = l_lean_ir_parse__key2val___main___rarg(x_0, x_9, x_2);
x_35 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_30, x_34);
return x_35;
}
else
{
lean::dec(x_0);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_30);
return x_26;
}
}
}
else
{
obj* x_41; uint8 x_43; obj* x_44; 
lean::dec(x_14);
x_41 = lean::cnstr_get(x_18, 0);
x_43 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_44 = x_18;
} else {
 lean::inc(x_41);
 lean::dec(x_18);
 x_44 = lean::box(0);
}
if (x_43 == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_44);
x_46 = l_lean_ir_parse__key2val___main___rarg(x_0, x_9, x_2);
x_47 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_0);
lean::dec(x_9);
lean::dec(x_2);
if (lean::is_scalar(x_44)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_44;
}
lean::cnstr_set(x_51, 0, x_41);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_43);
x_52 = x_51;
return x_52;
}
}
}
}
}
obj* l_lean_ir_parse__key2val___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___main___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_ir_parse__key2val___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__key2val___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_ir_parse__key2val___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__key2val(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_4, x_5, x_3, x_3, x_1);
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
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_12 = l_char_quote__core(x_10);
x_13 = l_char_has__repr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_16, x_18, x_17, x_17, x_1);
lean::dec(x_1);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::string_iterator_next(x_1);
x_24 = lean::box(0);
x_25 = lean::box_uint32(x_10);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
return x_26;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_true_decidable;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::string_iterator_next(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
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
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_ir_parse__literal___spec__8(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::string_iterator_next(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
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
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
x_46 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_44, x_45, x_43, x_43, x_0);
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
x_59 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_56, x_58, x_57, x_57, x_0);
x_40 = x_59;
goto lbl_41;
}
else
{
uint8 x_60; 
x_60 = 1;
x_49 = x_60;
goto lbl_50;
}
lbl_50:
{
uint32 x_61; uint8 x_62; 
x_61 = 102;
x_62 = x_47 <= x_61;
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_63 = l_char_quote__core(x_47);
x_64 = l_char_has__repr___closed__1;
x_65 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_67 = lean::string_append(x_65, x_64);
x_68 = lean::box(0);
x_69 = l_mjoin___rarg___closed__1;
x_70 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_67, x_69, x_68, x_68, x_0);
x_40 = x_70;
goto lbl_41;
}
else
{
if (x_49 == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = l_char_quote__core(x_47);
x_72 = l_char_has__repr___closed__1;
x_73 = lean::string_append(x_72, x_71);
lean::dec(x_71);
x_75 = lean::string_append(x_73, x_72);
x_76 = lean::box(0);
x_77 = l_mjoin___rarg___closed__1;
x_78 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_75, x_77, x_76, x_76, x_0);
x_40 = x_78;
goto lbl_41;
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::inc(x_0);
x_80 = lean::string_iterator_next(x_0);
x_81 = lean::box(0);
x_82 = lean::box_uint32(x_47);
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_80);
lean::cnstr_set(x_83, 2, x_81);
x_40 = x_83;
goto lbl_41;
}
}
}
}
lbl_41:
{
obj* x_84; obj* x_85; 
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_40);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_88; obj* x_90; obj* x_92; uint32 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; 
x_86 = lean::cnstr_get(x_85, 0);
x_88 = lean::cnstr_get(x_85, 1);
x_90 = lean::cnstr_get(x_85, 2);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
x_93 = lean::unbox_uint32(x_86);
x_94 = lean::uint32_to_nat(x_93);
x_95 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_96 = lean::nat_sub(x_94, x_95);
lean::dec(x_94);
x_98 = lean::mk_nat_obj(10u);
x_99 = lean::nat_add(x_98, x_96);
lean::dec(x_96);
if (lean::is_scalar(x_92)) {
 x_101 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_101 = x_92;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_88);
lean::cnstr_set(x_101, 2, x_84);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_101);
if (lean::obj_tag(x_102) == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_0);
x_104 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_102);
x_105 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
x_106 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_104, x_105);
return x_106;
}
else
{
obj* x_107; uint8 x_109; 
x_107 = lean::cnstr_get(x_102, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<uint8>(x_102, sizeof(void*)*1);
x_35 = x_102;
x_36 = x_107;
x_37 = x_109;
goto lbl_38;
}
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_115; obj* x_116; 
x_110 = lean::cnstr_get(x_85, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
if (lean::is_exclusive(x_85)) {
 x_113 = x_85;
} else {
 lean::inc(x_110);
 lean::dec(x_85);
 x_113 = lean::box(0);
}
lean::inc(x_110);
if (lean::is_scalar(x_113)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_113;
}
lean::cnstr_set(x_115, 0, x_110);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_112);
x_116 = x_115;
x_35 = x_116;
x_36 = x_110;
x_37 = x_112;
goto lbl_38;
}
}
}
else
{
obj* x_119; obj* x_120; 
lean::dec(x_0);
lean::dec(x_2);
x_119 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
x_120 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_119);
return x_120;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_122; uint8 x_124; 
lean::dec(x_35);
x_124 = lean::string_iterator_has_next(x_0);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_125 = lean::box(0);
x_126 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_127 = l_mjoin___rarg___closed__1;
x_128 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_126, x_127, x_125, x_125, x_0);
lean::dec(x_0);
x_122 = x_128;
goto lbl_123;
}
else
{
uint32 x_130; uint32 x_131; uint8 x_132; uint8 x_134; 
x_130 = lean::string_iterator_curr(x_0);
x_131 = 65;
x_134 = x_131 <= x_130;
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = l_char_quote__core(x_130);
x_136 = l_char_has__repr___closed__1;
x_137 = lean::string_append(x_136, x_135);
lean::dec(x_135);
x_139 = lean::string_append(x_137, x_136);
x_140 = lean::box(0);
x_141 = l_mjoin___rarg___closed__1;
x_142 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_139, x_141, x_140, x_140, x_0);
lean::dec(x_0);
x_122 = x_142;
goto lbl_123;
}
else
{
uint8 x_144; 
x_144 = 1;
x_132 = x_144;
goto lbl_133;
}
lbl_133:
{
uint32 x_145; uint8 x_146; 
x_145 = 70;
x_146 = x_130 <= x_145;
if (x_146 == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_147 = l_char_quote__core(x_130);
x_148 = l_char_has__repr___closed__1;
x_149 = lean::string_append(x_148, x_147);
lean::dec(x_147);
x_151 = lean::string_append(x_149, x_148);
x_152 = lean::box(0);
x_153 = l_mjoin___rarg___closed__1;
x_154 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_151, x_153, x_152, x_152, x_0);
lean::dec(x_0);
x_122 = x_154;
goto lbl_123;
}
else
{
if (x_132 == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_156 = l_char_quote__core(x_130);
x_157 = l_char_has__repr___closed__1;
x_158 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_160 = lean::string_append(x_158, x_157);
x_161 = lean::box(0);
x_162 = l_mjoin___rarg___closed__1;
x_163 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_160, x_162, x_161, x_161, x_0);
lean::dec(x_0);
x_122 = x_163;
goto lbl_123;
}
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_165 = lean::string_iterator_next(x_0);
x_166 = lean::box(0);
x_167 = lean::box_uint32(x_130);
x_168 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
lean::cnstr_set(x_168, 2, x_166);
x_122 = x_168;
goto lbl_123;
}
}
}
}
lbl_123:
{
obj* x_169; obj* x_170; 
x_169 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_122);
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
obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
x_31 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
x_32 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_31, x_0, x_5);
lean::dec(x_5);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_32);
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
obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_81; obj* x_83; uint32 x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_63 = lean::cnstr_get(x_62, 0);
x_65 = lean::cnstr_get(x_62, 1);
x_67 = lean::cnstr_get(x_62, 2);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_62);
 x_69 = lean::box(0);
}
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
lean::dec(x_83);
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_89 = lean::box_uint32(x_86);
if (lean::is_scalar(x_69)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_69;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_65);
lean::cnstr_set(x_90, 2, x_88);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_93);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_95);
return x_96;
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_47);
lean::dec(x_55);
lean::dec(x_39);
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
obj* x_114; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_47);
lean::dec(x_39);
x_114 = lean::cnstr_get(x_54, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_114);
 lean::dec(x_54);
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
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_119);
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_121);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_122);
return x_124;
}
}
else
{
obj* x_126; uint8 x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_39);
x_126 = lean::cnstr_get(x_46, 0);
x_128 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 x_129 = x_46;
} else {
 lean::inc(x_126);
 lean::dec(x_46);
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
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_132);
x_134 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_133);
return x_135;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_38, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 x_139 = x_38;
} else {
 lean::inc(x_136);
 lean::dec(x_38);
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
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_141);
x_143 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_143, x_142);
return x_144;
}
}
}
lbl_13:
{
uint32 x_146; uint32 x_147; uint8 x_148; 
lean::dec(x_12);
x_146 = 116;
x_147 = lean::unbox_uint32(x_3);
x_148 = x_147 == x_146;
if (x_148 == 0)
{
uint32 x_150; uint8 x_151; 
lean::dec(x_9);
x_150 = 120;
x_151 = x_147 == x_150;
if (x_151 == 0)
{
obj* x_152; 
x_152 = lean::box(0);
x_10 = x_152;
goto lbl_11;
}
else
{
obj* x_154; 
lean::dec(x_0);
x_154 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_5);
if (lean::obj_tag(x_154) == 0)
{
obj* x_155; obj* x_157; obj* x_159; obj* x_162; 
x_155 = lean::cnstr_get(x_154, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_154, 1);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_154, 2);
lean::inc(x_159);
lean::dec(x_154);
x_162 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_157);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_171; obj* x_173; uint32 x_176; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
x_163 = lean::cnstr_get(x_162, 0);
x_165 = lean::cnstr_get(x_162, 1);
x_167 = lean::cnstr_get(x_162, 2);
if (lean::is_exclusive(x_162)) {
 x_169 = x_162;
} else {
 lean::inc(x_163);
 lean::inc(x_165);
 lean::inc(x_167);
 lean::dec(x_162);
 x_169 = lean::box(0);
}
x_170 = lean::mk_nat_obj(16u);
x_171 = lean::nat_mul(x_170, x_155);
lean::dec(x_155);
x_173 = lean::nat_add(x_171, x_163);
lean::dec(x_163);
lean::dec(x_171);
x_176 = l_char_of__nat(x_173);
lean::dec(x_173);
x_178 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_179 = lean::box_uint32(x_176);
if (lean::is_scalar(x_169)) {
 x_180 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_180 = x_169;
}
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_180, 1, x_165);
lean::cnstr_set(x_180, 2, x_178);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_180);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_183);
return x_184;
}
else
{
obj* x_186; uint8 x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_155);
x_186 = lean::cnstr_get(x_162, 0);
x_188 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
if (lean::is_exclusive(x_162)) {
 x_189 = x_162;
} else {
 lean::inc(x_186);
 lean::dec(x_162);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_186);
lean::cnstr_set_scalar(x_190, sizeof(void*)*1, x_188);
x_191 = x_190;
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_191);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_192);
x_194 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_194, x_193);
return x_195;
}
}
else
{
obj* x_196; uint8 x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_196 = lean::cnstr_get(x_154, 0);
x_198 = lean::cnstr_get_scalar<uint8>(x_154, sizeof(void*)*1);
if (lean::is_exclusive(x_154)) {
 x_199 = x_154;
} else {
 lean::inc(x_196);
 lean::dec(x_154);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_196);
lean::cnstr_set_scalar(x_200, sizeof(void*)*1, x_198);
x_201 = x_200;
x_202 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_201);
x_203 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_204 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_202);
return x_204;
}
}
}
else
{
uint32 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_0);
x_206 = 9;
x_207 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_208 = lean::box_uint32(x_206);
if (lean::is_scalar(x_9)) {
 x_209 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_209 = x_9;
}
lean::cnstr_set(x_209, 0, x_208);
lean::cnstr_set(x_209, 1, x_5);
lean::cnstr_set(x_209, 2, x_207);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_207, x_210);
return x_211;
}
}
lbl_15:
{
uint32 x_213; uint32 x_214; uint8 x_215; 
lean::dec(x_14);
x_213 = 34;
x_214 = lean::unbox_uint32(x_3);
x_215 = x_214 == x_213;
if (x_215 == 0)
{
uint32 x_216; uint8 x_217; 
x_216 = 39;
x_217 = x_214 == x_216;
if (x_217 == 0)
{
uint32 x_218; uint8 x_219; 
x_218 = 110;
x_219 = x_214 == x_218;
if (x_219 == 0)
{
obj* x_220; 
x_220 = lean::box(0);
x_12 = x_220;
goto lbl_13;
}
else
{
uint32 x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_9);
lean::dec(x_0);
x_223 = 10;
x_224 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_225 = lean::box_uint32(x_223);
x_226 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_5);
lean::cnstr_set(x_226, 2, x_224);
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_226);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_224, x_227);
return x_228;
}
}
else
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_9);
lean::dec(x_0);
x_231 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_232 = lean::box_uint32(x_216);
x_233 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_5);
lean::cnstr_set(x_233, 2, x_231);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_233);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_234);
return x_235;
}
}
else
{
obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_9);
lean::dec(x_0);
x_238 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_239 = lean::box_uint32(x_213);
x_240 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_5);
lean::cnstr_set(x_240, 2, x_238);
x_241 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_240);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_238, x_241);
return x_242;
}
}
}
else
{
obj* x_244; uint8 x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_0);
x_244 = lean::cnstr_get(x_2, 0);
x_246 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_247 = x_2;
} else {
 lean::inc(x_244);
 lean::dec(x_2);
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
x_250 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_249);
return x_251;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; uint32 x_16; uint8 x_17; 
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
x_15 = 92;
x_16 = lean::unbox_uint32(x_6);
x_17 = x_16 == x_15;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; 
x_18 = 34;
x_19 = x_16 == x_18;
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_24; 
lean::dec(x_12);
x_21 = lean::string_push(x_1, x_16);
x_22 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_14, x_21, x_8);
lean::dec(x_14);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_22);
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
obj* x_31; obj* x_33; obj* x_35; uint32 x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
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
lean::dec(x_14);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_40);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_42);
return x_43;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_1);
lean::dec(x_14);
x_46 = lean::cnstr_get(x_30, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_exclusive(x_30)) {
 x_49 = x_30;
} else {
 lean::inc(x_46);
 lean::dec(x_30);
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
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_51);
return x_52;
}
}
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
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
uint32 x_60; obj* x_61; 
x_60 = 34;
x_61 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_60, x_2);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_61, 1);
x_64 = lean::cnstr_get(x_61, 2);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_68);
return x_69;
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_71 = lean::cnstr_get(x_61, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_74 = x_61;
} else {
 lean::inc(x_71);
 lean::dec(x_61);
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
return x_76;
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
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::string_iterator_remaining(x_3);
x_9 = l_string_join___closed__1;
x_10 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_8, x_9, x_3);
lean::dec(x_8);
x_12 = l_lean_ir_keyword___closed__1;
x_13 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_10);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_13);
return x_14;
}
else
{
obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_18 = x_2;
} else {
 lean::inc(x_15);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_17);
x_20 = x_19;
return x_20;
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
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_string_join___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__literal___spec__16(x_5, x_4, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_parse__literal___spec__10(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_17 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__11(x_16, x_11);
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
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_31, x_33, x_32, x_32, x_0);
lean::dec(x_0);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_42; uint32 x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 2);
lean::inc(x_42);
lean::dec(x_37);
x_45 = lean::unbox_uint32(x_38);
x_46 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(x_45, x_40);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_46);
return x_47;
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_37, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_51 = x_37;
} else {
 lean::inc(x_48);
 lean::dec(x_37);
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
obj* x_55; obj* x_56; obj* x_57; obj* x_59; 
lean::inc(x_0);
x_55 = lean::string_iterator_next(x_0);
x_56 = lean::box(0);
x_57 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(x_0, x_55);
lean::dec(x_0);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_57);
return x_59;
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
obj* x_64; obj* x_66; obj* x_68; obj* x_71; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_63, 2);
lean::inc(x_68);
lean::dec(x_63);
x_71 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_66);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_72 = lean::cnstr_get(x_71, 1);
x_74 = lean::cnstr_get(x_71, 2);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_76 = x_71;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_71);
 x_76 = lean::box(0);
}
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_76;
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
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_82, 0);
x_85 = lean::cnstr_get(x_82, 1);
x_87 = lean::cnstr_get(x_82, 2);
if (lean::is_exclusive(x_82)) {
 x_89 = x_82;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_82);
 x_89 = lean::box(0);
}
x_90 = lean::nat2int(x_83);
x_91 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
if (lean::is_scalar(x_89)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_89;
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
obj* x_100; uint8 x_102; obj* x_103; obj* x_105; obj* x_106; 
x_100 = lean::cnstr_get(x_82, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_exclusive(x_82)) {
 x_103 = x_82;
} else {
 lean::inc(x_100);
 lean::dec(x_82);
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
x_57 = x_106;
x_58 = x_100;
x_59 = x_102;
goto lbl_60;
}
}
else
{
obj* x_108; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_64);
x_108 = lean::cnstr_get(x_71, 0);
x_110 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_111 = x_71;
} else {
 lean::inc(x_108);
 lean::dec(x_71);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_108);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_110);
x_113 = x_112;
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_113);
x_115 = l_lean_ir_parse__literal___closed__1;
x_116 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_114, x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_117 = lean::cnstr_get(x_116, 0);
x_119 = lean::cnstr_get(x_116, 1);
x_121 = lean::cnstr_get(x_116, 2);
if (lean::is_exclusive(x_116)) {
 x_123 = x_116;
} else {
 lean::inc(x_117);
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = lean::nat2int(x_117);
x_125 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_125, 0, x_124);
x_126 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_123)) {
 x_127 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_127 = x_123;
}
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_119);
lean::cnstr_set(x_127, 2, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_127);
if (lean::obj_tag(x_128) == 0)
{
obj* x_130; obj* x_131; 
lean::dec(x_0);
x_130 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_128);
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_130);
return x_131;
}
else
{
obj* x_132; uint8 x_134; 
x_132 = lean::cnstr_get(x_128, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get_scalar<uint8>(x_128, sizeof(void*)*1);
x_57 = x_128;
x_58 = x_132;
x_59 = x_134;
goto lbl_60;
}
}
else
{
obj* x_135; uint8 x_137; obj* x_138; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_116, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_116, sizeof(void*)*1);
if (lean::is_exclusive(x_116)) {
 x_138 = x_116;
} else {
 lean::inc(x_135);
 lean::dec(x_116);
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
x_57 = x_141;
x_58 = x_135;
x_59 = x_137;
goto lbl_60;
}
}
}
else
{
obj* x_142; uint8 x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_142 = lean::cnstr_get(x_63, 0);
x_144 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (lean::is_exclusive(x_63)) {
 x_145 = x_63;
} else {
 lean::inc(x_142);
 lean::dec(x_63);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_142);
lean::cnstr_set_scalar(x_146, sizeof(void*)*1, x_144);
x_147 = x_146;
x_148 = l_lean_ir_parse__literal___closed__1;
x_149 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_147, x_148);
if (lean::obj_tag(x_149) == 0)
{
obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_150 = lean::cnstr_get(x_149, 0);
x_152 = lean::cnstr_get(x_149, 1);
x_154 = lean::cnstr_get(x_149, 2);
if (lean::is_exclusive(x_149)) {
 x_156 = x_149;
} else {
 lean::inc(x_150);
 lean::inc(x_152);
 lean::inc(x_154);
 lean::dec(x_149);
 x_156 = lean::box(0);
}
x_157 = lean::nat2int(x_150);
x_158 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_158, 0, x_157);
x_159 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_156)) {
 x_160 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_160 = x_156;
}
lean::cnstr_set(x_160, 0, x_158);
lean::cnstr_set(x_160, 1, x_152);
lean::cnstr_set(x_160, 2, x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_154, x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_163; obj* x_164; 
lean::dec(x_0);
x_163 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_161);
x_164 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_163);
return x_164;
}
else
{
obj* x_165; uint8 x_167; 
x_165 = lean::cnstr_get(x_161, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get_scalar<uint8>(x_161, sizeof(void*)*1);
x_57 = x_161;
x_58 = x_165;
x_59 = x_167;
goto lbl_60;
}
}
else
{
obj* x_168; uint8 x_170; obj* x_171; obj* x_173; obj* x_174; 
x_168 = lean::cnstr_get(x_149, 0);
x_170 = lean::cnstr_get_scalar<uint8>(x_149, sizeof(void*)*1);
if (lean::is_exclusive(x_149)) {
 x_171 = x_149;
} else {
 lean::inc(x_168);
 lean::dec(x_149);
 x_171 = lean::box(0);
}
lean::inc(x_168);
if (lean::is_scalar(x_171)) {
 x_173 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_173 = x_171;
}
lean::cnstr_set(x_173, 0, x_168);
lean::cnstr_set_scalar(x_173, sizeof(void*)*1, x_170);
x_174 = x_173;
x_57 = x_174;
x_58 = x_168;
x_59 = x_170;
goto lbl_60;
}
}
}
else
{
obj* x_177; 
lean::dec(x_0);
lean::dec(x_27);
x_177 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_26);
return x_177;
}
lbl_60:
{
obj* x_178; obj* x_179; obj* x_180; obj* x_182; uint8 x_183; 
if (x_59 == 0)
{
obj* x_187; 
lean::dec(x_57);
lean::inc(x_0);
x_187 = l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2(x_1, x_0);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_190; obj* x_193; 
x_188 = lean::cnstr_get(x_187, 1);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 2);
lean::inc(x_190);
lean::dec(x_187);
x_193 = l_lean_parser_monad__parsec_num___at_lean_ir_parse__literal___spec__9(x_188);
if (lean::obj_tag(x_193) == 0)
{
obj* x_194; obj* x_196; obj* x_198; obj* x_201; 
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_193, 2);
lean::inc(x_198);
lean::dec(x_193);
x_201 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_196);
if (lean::obj_tag(x_201) == 0)
{
obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_202 = lean::cnstr_get(x_201, 1);
x_204 = lean::cnstr_get(x_201, 2);
if (lean::is_exclusive(x_201)) {
 lean::cnstr_release(x_201, 0);
 x_206 = x_201;
} else {
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_201);
 x_206 = lean::box(0);
}
x_207 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_206)) {
 x_208 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_208 = x_206;
}
lean::cnstr_set(x_208, 0, x_194);
lean::cnstr_set(x_208, 1, x_202);
lean::cnstr_set(x_208, 2, x_207);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_204, x_208);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_198, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_210);
if (lean::obj_tag(x_211) == 0)
{
obj* x_212; obj* x_214; obj* x_216; 
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_211, 2);
lean::inc(x_216);
lean::dec(x_211);
x_178 = x_212;
x_179 = x_214;
x_180 = x_216;
goto lbl_181;
}
else
{
obj* x_219; uint8 x_221; 
x_219 = lean::cnstr_get(x_211, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get_scalar<uint8>(x_211, sizeof(void*)*1);
lean::dec(x_211);
x_182 = x_219;
x_183 = x_221;
goto lbl_184;
}
}
else
{
obj* x_224; uint8 x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
lean::dec(x_194);
x_224 = lean::cnstr_get(x_201, 0);
x_226 = lean::cnstr_get_scalar<uint8>(x_201, sizeof(void*)*1);
if (lean::is_exclusive(x_201)) {
 x_227 = x_201;
} else {
 lean::inc(x_224);
 lean::dec(x_201);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_224);
lean::cnstr_set_scalar(x_228, sizeof(void*)*1, x_226);
x_229 = x_228;
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_198, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_230);
if (lean::obj_tag(x_231) == 0)
{
obj* x_232; obj* x_234; obj* x_236; 
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_231, 1);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_231, 2);
lean::inc(x_236);
lean::dec(x_231);
x_178 = x_232;
x_179 = x_234;
x_180 = x_236;
goto lbl_181;
}
else
{
obj* x_239; uint8 x_241; 
x_239 = lean::cnstr_get(x_231, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get_scalar<uint8>(x_231, sizeof(void*)*1);
lean::dec(x_231);
x_182 = x_239;
x_183 = x_241;
goto lbl_184;
}
}
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_243 = lean::cnstr_get(x_193, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_193, sizeof(void*)*1);
if (lean::is_exclusive(x_193)) {
 x_246 = x_193;
} else {
 lean::inc(x_243);
 lean::dec(x_193);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_243);
lean::cnstr_set_scalar(x_247, sizeof(void*)*1, x_245);
x_248 = x_247;
x_249 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_248);
if (lean::obj_tag(x_249) == 0)
{
obj* x_250; obj* x_252; obj* x_254; 
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_249, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_249, 2);
lean::inc(x_254);
lean::dec(x_249);
x_178 = x_250;
x_179 = x_252;
x_180 = x_254;
goto lbl_181;
}
else
{
obj* x_257; uint8 x_259; 
x_257 = lean::cnstr_get(x_249, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get_scalar<uint8>(x_249, sizeof(void*)*1);
lean::dec(x_249);
x_182 = x_257;
x_183 = x_259;
goto lbl_184;
}
}
}
else
{
obj* x_261; uint8 x_263; 
x_261 = lean::cnstr_get(x_187, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*1);
lean::dec(x_187);
x_182 = x_261;
x_183 = x_263;
goto lbl_184;
}
}
else
{
obj* x_267; obj* x_268; 
lean::dec(x_58);
lean::dec(x_0);
x_267 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_57);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_267);
return x_268;
}
lbl_181:
{
obj* x_269; obj* x_270; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_269 = lean::nat2int(x_178);
x_270 = lean::int_neg(x_269);
lean::dec(x_269);
x_272 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_272, 0, x_270);
x_273 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_274 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_274, 0, x_272);
lean::cnstr_set(x_274, 1, x_179);
lean::cnstr_set(x_274, 2, x_273);
x_275 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_180, x_274);
if (lean::obj_tag(x_275) == 0)
{
obj* x_277; obj* x_278; obj* x_279; 
lean::dec(x_0);
x_277 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_275);
x_278 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_277);
x_279 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_278);
return x_279;
}
else
{
obj* x_280; uint8 x_282; 
x_280 = lean::cnstr_get(x_275, 0);
lean::inc(x_280);
x_282 = lean::cnstr_get_scalar<uint8>(x_275, sizeof(void*)*1);
if (x_282 == 0)
{
obj* x_284; 
lean::dec(x_275);
x_284 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_284) == 0)
{
obj* x_285; obj* x_287; obj* x_289; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; 
x_285 = lean::cnstr_get(x_284, 0);
x_287 = lean::cnstr_get(x_284, 1);
x_289 = lean::cnstr_get(x_284, 2);
if (lean::is_exclusive(x_284)) {
 x_291 = x_284;
} else {
 lean::inc(x_285);
 lean::inc(x_287);
 lean::inc(x_289);
 lean::dec(x_284);
 x_291 = lean::box(0);
}
x_292 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_292, 0, x_285);
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_287);
lean::cnstr_set(x_293, 2, x_273);
x_294 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_289, x_293);
x_295 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_280, x_294);
x_296 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_295);
x_297 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_296);
x_298 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_297);
return x_298;
}
else
{
obj* x_299; uint8 x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; 
x_299 = lean::cnstr_get(x_284, 0);
x_301 = lean::cnstr_get_scalar<uint8>(x_284, sizeof(void*)*1);
if (lean::is_exclusive(x_284)) {
 x_302 = x_284;
} else {
 lean::inc(x_299);
 lean::dec(x_284);
 x_302 = lean::box(0);
}
if (lean::is_scalar(x_302)) {
 x_303 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_303 = x_302;
}
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set_scalar(x_303, sizeof(void*)*1, x_301);
x_304 = x_303;
x_305 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_280, x_304);
x_306 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_305);
x_307 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_306);
x_308 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_307);
return x_308;
}
}
else
{
obj* x_311; obj* x_312; obj* x_313; 
lean::dec(x_0);
lean::dec(x_280);
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_275);
x_312 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_311);
x_313 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_312);
return x_313;
}
}
}
lbl_184:
{
if (x_183 == 0)
{
obj* x_314; 
x_314 = l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(x_0);
if (lean::obj_tag(x_314) == 0)
{
obj* x_315; obj* x_317; obj* x_319; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
x_315 = lean::cnstr_get(x_314, 0);
x_317 = lean::cnstr_get(x_314, 1);
x_319 = lean::cnstr_get(x_314, 2);
if (lean::is_exclusive(x_314)) {
 x_321 = x_314;
} else {
 lean::inc(x_315);
 lean::inc(x_317);
 lean::inc(x_319);
 lean::dec(x_314);
 x_321 = lean::box(0);
}
x_322 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_322, 0, x_315);
x_323 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_321)) {
 x_324 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_324 = x_321;
}
lean::cnstr_set(x_324, 0, x_322);
lean::cnstr_set(x_324, 1, x_317);
lean::cnstr_set(x_324, 2, x_323);
x_325 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_319, x_324);
x_326 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_182, x_325);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_326);
x_328 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_327);
x_329 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_328);
return x_329;
}
else
{
obj* x_330; uint8 x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; 
x_330 = lean::cnstr_get(x_314, 0);
x_332 = lean::cnstr_get_scalar<uint8>(x_314, sizeof(void*)*1);
if (lean::is_exclusive(x_314)) {
 x_333 = x_314;
} else {
 lean::inc(x_330);
 lean::dec(x_314);
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
x_336 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_182, x_335);
x_337 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_336);
x_338 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_337);
x_339 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_338);
return x_339;
}
}
else
{
obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_0);
x_341 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_341, 0, x_182);
lean::cnstr_set_scalar(x_341, sizeof(void*)*1, x_183);
x_342 = x_341;
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_58, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_27, x_343);
x_345 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_23, x_344);
return x_345;
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
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__string__literal__aux___main___at_lean_ir_parse__literal___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_14, 1);
x_17 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_19;
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
obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_7);
x_43 = lean::cnstr_get(x_14, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_46 = x_14;
} else {
 lean::inc(x_43);
 lean::dec(x_14);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_54; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 2);
lean::inc(x_54);
lean::dec(x_49);
x_1 = x_50;
x_2 = x_52;
x_3 = x_54;
goto lbl_4;
}
else
{
obj* x_58; uint8 x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_58 = lean::cnstr_get(x_49, 0);
x_60 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (lean::is_exclusive(x_49)) {
 x_61 = x_49;
} else {
 lean::inc(x_58);
 lean::dec(x_49);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_60);
x_63 = x_62;
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_63);
x_66 = l_lean_parser_parsec__t_try__mk__res___rarg(x_65);
x_67 = l_lean_ir_parse__uint16___closed__1;
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_66, x_67);
return x_68;
}
}
}
else
{
obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_0);
x_70 = lean::cnstr_get(x_6, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_73 = x_6;
} else {
 lean::inc(x_70);
 lean::dec(x_6);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_75);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
x_79 = l_lean_ir_parse__uint16___closed__1;
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_78, x_79);
return x_80;
}
lbl_4:
{
obj* x_81; uint8 x_82; 
x_81 = l_uint16__sz;
x_82 = lean::nat_dec_le(x_81, x_1);
if (x_82 == 0)
{
uint16 x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_0);
x_84 = lean::uint16_of_nat(x_1);
lean::dec(x_1);
x_86 = l_lean_ir_keyword___closed__1;
x_87 = lean::box(x_84);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_2);
lean::cnstr_set(x_88, 2, x_86);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_88);
x_90 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_89);
x_92 = l_lean_parser_parsec__t_try__mk__res___rarg(x_91);
x_93 = l_lean_ir_parse__uint16___closed__1;
x_94 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_92, x_93);
return x_94;
}
else
{
obj* x_95; obj* x_96; 
x_95 = l_lean_ir_parse__uint16___closed__2;
x_96 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_95, x_0, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_96) == 0)
{
obj* x_98; obj* x_100; obj* x_102; uint16 x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_98 = lean::cnstr_get(x_96, 1);
x_100 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_102 = x_96;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_96);
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
x_115 = lean::cnstr_get(x_96, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_118 = x_96;
} else {
 lean::inc(x_115);
 lean::dec(x_96);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_14; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_14, 1);
x_17 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_19;
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
obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_7);
x_43 = lean::cnstr_get(x_14, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_46 = x_14;
} else {
 lean::inc(x_43);
 lean::dec(x_14);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_54; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 2);
lean::inc(x_54);
lean::dec(x_49);
x_1 = x_50;
x_2 = x_52;
x_3 = x_54;
goto lbl_4;
}
else
{
obj* x_58; uint8 x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_0);
x_58 = lean::cnstr_get(x_49, 0);
x_60 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (lean::is_exclusive(x_49)) {
 x_61 = x_49;
} else {
 lean::inc(x_58);
 lean::dec(x_49);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_60);
x_63 = x_62;
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_63);
x_66 = l_lean_parser_parsec__t_try__mk__res___rarg(x_65);
x_67 = l_lean_ir_parse__usize___closed__1;
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_66, x_67);
return x_68;
}
}
}
else
{
obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_0);
x_70 = lean::cnstr_get(x_6, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_73 = x_6;
} else {
 lean::inc(x_70);
 lean::dec(x_6);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_75);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
x_79 = l_lean_ir_parse__usize___closed__1;
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_78, x_79);
return x_80;
}
lbl_4:
{
obj* x_81; uint8 x_82; 
x_81 = l_usize__sz;
x_82 = lean::nat_dec_le(x_81, x_1);
if (x_82 == 0)
{
usize x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_0);
x_84 = lean::usize_of_nat(x_1);
lean::dec(x_1);
x_86 = l_lean_ir_keyword___closed__1;
x_87 = lean::box_size_t(x_84);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_2);
lean::cnstr_set(x_88, 2, x_86);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_88);
x_90 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_89);
x_92 = l_lean_parser_parsec__t_try__mk__res___rarg(x_91);
x_93 = l_lean_ir_parse__usize___closed__1;
x_94 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_92, x_93);
return x_94;
}
else
{
obj* x_95; obj* x_96; 
x_95 = l_lean_ir_parse__usize___closed__2;
x_96 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_95, x_0, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_96) == 0)
{
obj* x_98; obj* x_100; obj* x_102; usize x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_98 = lean::cnstr_get(x_96, 1);
x_100 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_102 = x_96;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_96);
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
x_115 = lean::cnstr_get(x_96, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_118 = x_96;
} else {
 lean::inc(x_115);
 lean::dec(x_96);
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
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_string_join___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__10(x_5, x_4, x_1);
return x_6;
}
}
obj* l_lean_parser_id__part__default___at_lean_ir_identifier___spec__4(obj* x_0) {
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
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_17 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(x_16, x_11);
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
x_26 = l_lean_is__id__first(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_31, x_33, x_32, x_32, x_0);
lean::dec(x_0);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_42; uint32 x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 2);
lean::inc(x_42);
lean::dec(x_37);
x_45 = lean::unbox_uint32(x_38);
x_46 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(x_45, x_40);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_46);
return x_47;
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_37, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_51 = x_37;
} else {
 lean::inc(x_48);
 lean::dec(x_37);
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
obj* x_55; obj* x_56; obj* x_57; obj* x_59; 
lean::inc(x_0);
x_55 = lean::string_iterator_next(x_0);
x_56 = lean::box(0);
x_57 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(x_0, x_55);
lean::dec(x_0);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_57);
return x_59;
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
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_string_join___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(x_5, x_4, x_1);
return x_6;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_3, x_4, x_2, x_2, x_0);
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
x_17 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__13(x_16, x_11);
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
x_26 = l_lean_is__id__end__escape(x_25);
if (x_26 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
lean::inc(x_0);
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15(x_0, x_28);
lean::dec(x_0);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_30);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_33 = l_char_quote__core(x_25);
x_34 = l_char_has__repr___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_37 = lean::string_append(x_35, x_34);
x_38 = lean::box(0);
x_39 = l_mjoin___rarg___closed__1;
x_40 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_37, x_39, x_38, x_38, x_0);
lean::dec(x_0);
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_46; obj* x_48; uint32 x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_43, 2);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::unbox_uint32(x_44);
x_52 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(x_51, x_46);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_52);
return x_53;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_43, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (lean::is_exclusive(x_43)) {
 x_57 = x_43;
} else {
 lean::inc(x_54);
 lean::dec(x_43);
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
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
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
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_19 = lean::cnstr_get(x_18, 1);
x_21 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_23 = x_18;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_18);
 x_23 = lean::box(0);
}
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_23;
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
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_10);
x_29 = lean::cnstr_get(x_18, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_32 = x_18;
} else {
 lean::inc(x_29);
 lean::dec(x_18);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_34);
return x_35;
}
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; 
x_36 = lean::cnstr_get(x_9, 0);
x_38 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_39 = x_9;
} else {
 lean::inc(x_36);
 lean::dec(x_9);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_38);
x_41 = x_40;
return x_41;
}
}
else
{
obj* x_42; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_2, 0);
x_44 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_45 = x_2;
} else {
 lean::inc(x_42);
 lean::dec(x_2);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_44);
x_47 = x_46;
return x_47;
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
obj* x_15; uint8 x_17; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_20; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_14, 2);
lean::inc(x_20);
lean::dec(x_14);
x_23 = l_lean_parser_id__part__default___at_lean_ir_identifier___spec__4(x_18);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_14, 2);
lean::inc(x_27);
lean::dec(x_14);
x_30 = l_lean_parser_id__part__escaped___at_lean_ir_identifier___spec__11(x_25);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_30);
return x_31;
}
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_14, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_35 = x_14;
} else {
 lean::inc(x_32);
 lean::dec(x_14);
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
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; 
x_38 = lean::cnstr_get(x_1, 0);
x_40 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_41 = x_1;
} else {
 lean::inc(x_38);
 lean::dec(x_1);
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
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
lean::dec(x_12);
x_16 = lean::cnstr_get(x_14, 0);
x_18 = lean::cnstr_get(x_14, 1);
x_20 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 lean::cnstr_set(x_14, 2, lean::box(0));
 x_22 = x_14;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_14);
 x_22 = lean::box(0);
}
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_sub(x_1, x_23);
lean::inc(x_0);
x_26 = lean_name_mk_string(x_0, x_16);
x_27 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_26, x_24, x_18);
lean::dec(x_24);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_27);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_22);
return x_29;
}
else
{
obj* x_33; uint8 x_35; 
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (x_35 == 0)
{
obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_29);
x_37 = lean::cnstr_get(x_33, 2);
lean::inc(x_37);
lean::dec(x_33);
x_40 = l_mjoin___rarg___closed__1;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_41, 0, x_37);
lean::closure_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
if (lean::is_scalar(x_22)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_22;
}
lean::cnstr_set(x_43, 0, x_0);
lean::cnstr_set(x_43, 1, x_2);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_22);
lean::dec(x_33);
return x_29;
}
}
}
else
{
obj* x_48; uint8 x_50; obj* x_51; 
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
obj* x_65; uint8 x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_7, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_68 = x_7;
} else {
 lean::inc(x_65);
 lean::dec(x_7);
 x_68 = lean::box(0);
}
if (x_67 == 0)
{
obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_68);
x_70 = lean::cnstr_get(x_65, 2);
lean::inc(x_70);
lean::dec(x_65);
x_73 = l_mjoin___rarg___closed__1;
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_74, 0, x_70);
lean::closure_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_0);
lean::cnstr_set(x_76, 1, x_2);
lean::cnstr_set(x_76, 2, x_75);
return x_76;
}
else
{
obj* x_79; obj* x_80; 
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_68)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_68;
}
lean::cnstr_set(x_79, 0, x_65);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_67);
x_80 = x_79;
return x_80;
}
}
}
else
{
obj* x_81; obj* x_82; 
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_0);
lean::cnstr_set(x_82, 1, x_2);
lean::cnstr_set(x_82, 2, x_81);
return x_82;
}
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_ir_identifier___spec__19(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = lean_name_mk_string(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_3, x_4, x_1);
lean::dec(x_4);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; 
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
x_10 = l_lean_ir_is__reserved__name___main(x_3);
if (x_10 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_0);
x_12 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_5);
lean::cnstr_set(x_13, 2, x_12);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_13);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_14);
x_17 = l_lean_parser_parsec__t_try__mk__res___rarg(x_16);
x_18 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_19 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_17, x_18);
return x_19;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_9);
x_21 = l_lean_ir_identifier___closed__1;
x_22 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_21, x_0, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_24 = lean::cnstr_get(x_22, 1);
x_26 = lean::cnstr_get(x_22, 2);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_28 = x_22;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_22);
 x_28 = lean::box(0);
}
x_29 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_31);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_32);
x_34 = l_lean_parser_parsec__t_try__mk__res___rarg(x_33);
x_35 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_36 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_34, x_35);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__15(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_0, x_1, x_2);
lean::dec(x_1);
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
obj* x_2; obj* x_4; obj* x_6; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_14;
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
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_2);
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_25 = x_9;
} else {
 lean::inc(x_22);
 lean::dec(x_9);
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
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_27);
x_29 = l_lean_ir_parse__var___closed__1;
x_30 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_29);
return x_30;
}
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_34 = x_1;
} else {
 lean::inc(x_31);
 lean::dec(x_1);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_37 = l_lean_ir_parse__var___closed__1;
x_38 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_36, x_37);
return x_38;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_14;
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
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_2);
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_25 = x_9;
} else {
 lean::inc(x_22);
 lean::dec(x_9);
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
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_27);
x_29 = l_lean_ir_parse__fnid___closed__1;
x_30 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_29);
return x_30;
}
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_34 = x_1;
} else {
 lean::inc(x_31);
 lean::dec(x_1);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_37 = l_lean_ir_parse__fnid___closed__1;
x_38 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_36, x_37);
return x_38;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_14;
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
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_2);
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_25 = x_9;
} else {
 lean::inc(x_22);
 lean::dec(x_9);
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
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_27);
x_29 = l_lean_ir_parse__blockid___closed__1;
x_30 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_29);
return x_30;
}
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_34 = x_1;
} else {
 lean::inc(x_31);
 lean::dec(x_1);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_37 = l_lean_ir_parse__blockid___closed__1;
x_38 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_36, x_37);
return x_38;
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
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_ir_parse__typed__assignment___closed__2;
x_10 = l_lean_ir_str2type;
x_11 = l_lean_ir_parse__key2val___main___rarg(x_9, x_10, x_4);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_11, 2);
lean::inc(x_16);
lean::dec(x_11);
x_19 = l_lean_ir_parse__typed__assignment___closed__3;
x_20 = l_lean_ir_symbol(x_19, x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_32 = l_lean_ir_parse__typed__assignment___closed__6;
lean::inc(x_21);
x_34 = l_lean_ir_keyword(x_32, x_21);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; obj* x_40; 
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 2);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_lean_ir_parse__var(x_35);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_41 = lean::cnstr_get(x_40, 0);
x_43 = lean::cnstr_get(x_40, 1);
x_45 = lean::cnstr_get(x_40, 2);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__3___boxed), 4, 3);
lean::closure_set(x_50, 0, x_0);
lean::closure_set(x_50, 1, x_12);
lean::closure_set(x_50, 2, x_41);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_47;
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
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_68 = lean::cnstr_get(x_40, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 x_71 = x_40;
} else {
 lean::inc(x_68);
 lean::dec(x_40);
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
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; 
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 2);
lean::inc(x_79);
lean::dec(x_74);
x_28 = x_75;
x_29 = x_77;
x_30 = x_79;
goto lbl_31;
}
else
{
obj* x_82; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; 
x_82 = lean::cnstr_get(x_74, 0);
x_84 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_85 = x_74;
} else {
 lean::inc(x_82);
 lean::dec(x_74);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*1, x_84);
x_87 = x_86;
x_26 = x_87;
goto lbl_27;
}
}
}
else
{
obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; 
x_88 = lean::cnstr_get(x_34, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
if (lean::is_exclusive(x_34)) {
 x_91 = x_34;
} else {
 lean::inc(x_88);
 lean::dec(x_34);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
x_26 = x_93;
goto lbl_27;
}
lbl_27:
{
if (lean::obj_tag(x_26) == 0)
{
obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_98);
return x_99;
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; uint8 x_105; 
x_100 = lean::cnstr_get(x_26, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_102 == 0)
{
obj* x_109; 
lean::dec(x_26);
lean::inc(x_21);
x_109 = l_lean_ir_parse__var(x_21);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_110 = lean::cnstr_get(x_109, 0);
x_112 = lean::cnstr_get(x_109, 1);
x_114 = lean::cnstr_get(x_109, 2);
if (lean::is_exclusive(x_109)) {
 x_116 = x_109;
} else {
 lean::inc(x_110);
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_109);
 x_116 = lean::box(0);
}
lean::inc(x_0);
x_118 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_118, 0, x_0);
lean::cnstr_set(x_118, 1, x_110);
x_119 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_118, sizeof(void*)*2, x_119);
x_120 = x_118;
x_121 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_116)) {
 x_122 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_122 = x_116;
}
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_112);
lean::cnstr_set(x_122, 2, x_121);
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_0);
lean::dec(x_21);
x_126 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_123);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_127);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_128);
return x_129;
}
else
{
obj* x_130; uint8 x_132; 
x_130 = lean::cnstr_get(x_123, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*1);
x_103 = x_123;
x_104 = x_130;
x_105 = x_132;
goto lbl_106;
}
}
else
{
obj* x_133; uint8 x_135; obj* x_136; obj* x_138; obj* x_139; 
x_133 = lean::cnstr_get(x_109, 0);
x_135 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_exclusive(x_109)) {
 x_136 = x_109;
} else {
 lean::inc(x_133);
 lean::dec(x_109);
 x_136 = lean::box(0);
}
lean::inc(x_133);
if (lean::is_scalar(x_136)) {
 x_138 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_138 = x_136;
}
lean::cnstr_set(x_138, 0, x_133);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_135);
x_139 = x_138;
x_103 = x_139;
x_104 = x_133;
x_105 = x_135;
goto lbl_106;
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_100);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_145);
return x_146;
}
lbl_106:
{
obj* x_147; obj* x_148; uint8 x_149; 
if (x_105 == 0)
{
obj* x_152; obj* x_153; obj* x_155; 
lean::dec(x_103);
x_152 = l_lean_ir_parse__typed__assignment___closed__5;
x_153 = l_lean_ir_str2aunop;
lean::inc(x_21);
x_155 = l_lean_ir_parse__key2val___main___rarg(x_152, x_153, x_21);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_158; obj* x_160; obj* x_162; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_156 = lean::cnstr_get(x_155, 0);
x_158 = lean::cnstr_get(x_155, 1);
x_160 = lean::cnstr_get(x_155, 2);
if (lean::is_exclusive(x_155)) {
 x_162 = x_155;
} else {
 lean::inc(x_156);
 lean::inc(x_158);
 lean::inc(x_160);
 lean::dec(x_155);
 x_162 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_165 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__2___boxed), 4, 3);
lean::closure_set(x_165, 0, x_0);
lean::closure_set(x_165, 1, x_12);
lean::closure_set(x_165, 2, x_156);
x_166 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_162)) {
 x_167 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_167 = x_162;
}
lean::cnstr_set(x_167, 0, x_165);
lean::cnstr_set(x_167, 1, x_158);
lean::cnstr_set(x_167, 2, x_166);
x_168 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_160, x_167);
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
x_176 = l_lean_ir_parse__var(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
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
x_184 = lean::apply_1(x_169, x_177);
if (lean::is_scalar(x_183)) {
 x_185 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_185 = x_183;
}
lean::cnstr_set(x_185, 0, x_184);
lean::cnstr_set(x_185, 1, x_179);
lean::cnstr_set(x_185, 2, x_166);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_186);
if (lean::obj_tag(x_187) == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_191 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_187);
x_192 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_191);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_192);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_193);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_194);
return x_195;
}
else
{
obj* x_196; uint8 x_198; 
x_196 = lean::cnstr_get(x_187, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*1);
x_147 = x_187;
x_148 = x_196;
x_149 = x_198;
goto lbl_150;
}
}
else
{
obj* x_200; uint8 x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
lean::dec(x_169);
x_200 = lean::cnstr_get(x_176, 0);
x_202 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
 x_203 = x_176;
} else {
 lean::inc(x_200);
 lean::dec(x_176);
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
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_205);
if (lean::obj_tag(x_206) == 0)
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_210 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_206);
x_211 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_212);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_213);
return x_214;
}
else
{
obj* x_215; uint8 x_217; 
x_215 = lean::cnstr_get(x_206, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get_scalar<uint8>(x_206, sizeof(void*)*1);
x_147 = x_206;
x_148 = x_215;
x_149 = x_217;
goto lbl_150;
}
}
}
else
{
obj* x_218; uint8 x_220; obj* x_221; obj* x_223; obj* x_224; 
x_218 = lean::cnstr_get(x_168, 0);
x_220 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_exclusive(x_168)) {
 x_221 = x_168;
} else {
 lean::inc(x_218);
 lean::dec(x_168);
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
x_147 = x_224;
x_148 = x_218;
x_149 = x_220;
goto lbl_150;
}
}
else
{
obj* x_225; uint8 x_227; obj* x_228; obj* x_230; obj* x_231; 
x_225 = lean::cnstr_get(x_155, 0);
x_227 = lean::cnstr_get_scalar<uint8>(x_155, sizeof(void*)*1);
if (lean::is_exclusive(x_155)) {
 x_228 = x_155;
} else {
 lean::inc(x_225);
 lean::dec(x_155);
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
x_147 = x_231;
x_148 = x_225;
x_149 = x_227;
goto lbl_150;
}
}
else
{
obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_0);
lean::dec(x_104);
lean::dec(x_12);
lean::dec(x_21);
x_236 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_103);
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_236);
x_238 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_237);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_238);
return x_239;
}
lbl_150:
{
obj* x_240; obj* x_241; uint8 x_242; obj* x_244; obj* x_245; obj* x_246; 
if (x_149 == 0)
{
obj* x_249; obj* x_250; obj* x_252; 
lean::dec(x_147);
x_249 = l_lean_ir_parse__typed__assignment___closed__4;
x_250 = l_lean_ir_str2abinop;
lean::inc(x_21);
x_252 = l_lean_ir_parse__key2val___main___rarg(x_249, x_250, x_21);
if (lean::obj_tag(x_252) == 0)
{
obj* x_253; obj* x_255; obj* x_257; obj* x_259; obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
x_253 = lean::cnstr_get(x_252, 0);
x_255 = lean::cnstr_get(x_252, 1);
x_257 = lean::cnstr_get(x_252, 2);
if (lean::is_exclusive(x_252)) {
 x_259 = x_252;
} else {
 lean::inc(x_253);
 lean::inc(x_255);
 lean::inc(x_257);
 lean::dec(x_252);
 x_259 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_262 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__1___boxed), 5, 3);
lean::closure_set(x_262, 0, x_0);
lean::closure_set(x_262, 1, x_12);
lean::closure_set(x_262, 2, x_253);
x_263 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_259)) {
 x_264 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_264 = x_259;
}
lean::cnstr_set(x_264, 0, x_262);
lean::cnstr_set(x_264, 1, x_255);
lean::cnstr_set(x_264, 2, x_263);
x_265 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_264);
if (lean::obj_tag(x_265) == 0)
{
obj* x_266; obj* x_268; obj* x_270; obj* x_273; 
x_266 = lean::cnstr_get(x_265, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get(x_265, 1);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_265, 2);
lean::inc(x_270);
lean::dec(x_265);
x_273 = l_lean_ir_parse__var(x_268);
if (lean::obj_tag(x_273) == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_274 = lean::cnstr_get(x_273, 0);
x_276 = lean::cnstr_get(x_273, 1);
x_278 = lean::cnstr_get(x_273, 2);
if (lean::is_exclusive(x_273)) {
 x_280 = x_273;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::inc(x_278);
 lean::dec(x_273);
 x_280 = lean::box(0);
}
x_281 = lean::apply_1(x_266, x_274);
if (lean::is_scalar(x_280)) {
 x_282 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_282 = x_280;
}
lean::cnstr_set(x_282, 0, x_281);
lean::cnstr_set(x_282, 1, x_276);
lean::cnstr_set(x_282, 2, x_263);
x_283 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_278, x_282);
x_284 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_270, x_283);
if (lean::obj_tag(x_284) == 0)
{
obj* x_285; obj* x_287; obj* x_289; 
x_285 = lean::cnstr_get(x_284, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_284, 1);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_284, 2);
lean::inc(x_289);
lean::dec(x_284);
x_244 = x_285;
x_245 = x_287;
x_246 = x_289;
goto lbl_247;
}
else
{
obj* x_292; uint8 x_294; obj* x_295; obj* x_297; obj* x_298; 
x_292 = lean::cnstr_get(x_284, 0);
x_294 = lean::cnstr_get_scalar<uint8>(x_284, sizeof(void*)*1);
if (lean::is_exclusive(x_284)) {
 x_295 = x_284;
} else {
 lean::inc(x_292);
 lean::dec(x_284);
 x_295 = lean::box(0);
}
lean::inc(x_292);
if (lean::is_scalar(x_295)) {
 x_297 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_297 = x_295;
}
lean::cnstr_set(x_297, 0, x_292);
lean::cnstr_set_scalar(x_297, sizeof(void*)*1, x_294);
x_298 = x_297;
x_240 = x_298;
x_241 = x_292;
x_242 = x_294;
goto lbl_243;
}
}
else
{
obj* x_300; uint8 x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
lean::dec(x_266);
x_300 = lean::cnstr_get(x_273, 0);
x_302 = lean::cnstr_get_scalar<uint8>(x_273, sizeof(void*)*1);
if (lean::is_exclusive(x_273)) {
 x_303 = x_273;
} else {
 lean::inc(x_300);
 lean::dec(x_273);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_300);
lean::cnstr_set_scalar(x_304, sizeof(void*)*1, x_302);
x_305 = x_304;
x_306 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_270, x_305);
if (lean::obj_tag(x_306) == 0)
{
obj* x_307; obj* x_309; obj* x_311; 
x_307 = lean::cnstr_get(x_306, 0);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_306, 1);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_306, 2);
lean::inc(x_311);
lean::dec(x_306);
x_244 = x_307;
x_245 = x_309;
x_246 = x_311;
goto lbl_247;
}
else
{
obj* x_314; uint8 x_316; obj* x_317; obj* x_319; obj* x_320; 
x_314 = lean::cnstr_get(x_306, 0);
x_316 = lean::cnstr_get_scalar<uint8>(x_306, sizeof(void*)*1);
if (lean::is_exclusive(x_306)) {
 x_317 = x_306;
} else {
 lean::inc(x_314);
 lean::dec(x_306);
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
x_240 = x_320;
x_241 = x_314;
x_242 = x_316;
goto lbl_243;
}
}
}
else
{
obj* x_321; uint8 x_323; obj* x_324; obj* x_326; obj* x_327; 
x_321 = lean::cnstr_get(x_265, 0);
x_323 = lean::cnstr_get_scalar<uint8>(x_265, sizeof(void*)*1);
if (lean::is_exclusive(x_265)) {
 x_324 = x_265;
} else {
 lean::inc(x_321);
 lean::dec(x_265);
 x_324 = lean::box(0);
}
lean::inc(x_321);
if (lean::is_scalar(x_324)) {
 x_326 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_326 = x_324;
}
lean::cnstr_set(x_326, 0, x_321);
lean::cnstr_set_scalar(x_326, sizeof(void*)*1, x_323);
x_327 = x_326;
x_240 = x_327;
x_241 = x_321;
x_242 = x_323;
goto lbl_243;
}
}
else
{
obj* x_328; uint8 x_330; obj* x_331; obj* x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_252, 0);
x_330 = lean::cnstr_get_scalar<uint8>(x_252, sizeof(void*)*1);
if (lean::is_exclusive(x_252)) {
 x_331 = x_252;
} else {
 lean::inc(x_328);
 lean::dec(x_252);
 x_331 = lean::box(0);
}
lean::inc(x_328);
if (lean::is_scalar(x_331)) {
 x_333 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_333 = x_331;
}
lean::cnstr_set(x_333, 0, x_328);
lean::cnstr_set_scalar(x_333, sizeof(void*)*1, x_330);
x_334 = x_333;
x_240 = x_334;
x_241 = x_328;
x_242 = x_330;
goto lbl_243;
}
}
else
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
lean::dec(x_148);
x_339 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_147);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_339);
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_342);
return x_343;
}
lbl_243:
{
if (x_242 == 0)
{
obj* x_345; 
lean::dec(x_240);
x_345 = l_lean_ir_parse__literal(x_21);
if (lean::obj_tag(x_345) == 0)
{
obj* x_346; obj* x_348; obj* x_350; obj* x_352; obj* x_353; uint8 x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
x_346 = lean::cnstr_get(x_345, 0);
x_348 = lean::cnstr_get(x_345, 1);
x_350 = lean::cnstr_get(x_345, 2);
if (lean::is_exclusive(x_345)) {
 x_352 = x_345;
} else {
 lean::inc(x_346);
 lean::inc(x_348);
 lean::inc(x_350);
 lean::dec(x_345);
 x_352 = lean::box(0);
}
x_353 = lean::alloc_cnstr(1, 2, 1);
lean::cnstr_set(x_353, 0, x_0);
lean::cnstr_set(x_353, 1, x_346);
x_354 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_353, sizeof(void*)*2, x_354);
x_355 = x_353;
x_356 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_352)) {
 x_357 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_357 = x_352;
}
lean::cnstr_set(x_357, 0, x_355);
lean::cnstr_set(x_357, 1, x_348);
lean::cnstr_set(x_357, 2, x_356);
x_358 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_350, x_357);
x_359 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_241, x_358);
x_360 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_359);
x_361 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_360);
x_362 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_361);
x_363 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_362);
x_364 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_363);
x_365 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_364);
return x_365;
}
else
{
obj* x_368; uint8 x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
lean::dec(x_0);
lean::dec(x_12);
x_368 = lean::cnstr_get(x_345, 0);
x_370 = lean::cnstr_get_scalar<uint8>(x_345, sizeof(void*)*1);
if (lean::is_exclusive(x_345)) {
 x_371 = x_345;
} else {
 lean::inc(x_368);
 lean::dec(x_345);
 x_371 = lean::box(0);
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_368);
lean::cnstr_set_scalar(x_372, sizeof(void*)*1, x_370);
x_373 = x_372;
x_374 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_241, x_373);
x_375 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_374);
x_376 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_375);
x_377 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_376);
x_378 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_377);
x_379 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_378);
x_380 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_379);
return x_380;
}
}
else
{
obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
lean::dec(x_0);
lean::dec(x_241);
lean::dec(x_12);
lean::dec(x_21);
x_385 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_240);
x_386 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_385);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_386);
x_388 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_387);
x_389 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_388);
x_390 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_389);
return x_390;
}
}
lbl_247:
{
obj* x_391; 
x_391 = l_lean_ir_parse__var(x_245);
if (lean::obj_tag(x_391) == 0)
{
obj* x_392; obj* x_394; obj* x_396; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; 
x_392 = lean::cnstr_get(x_391, 0);
x_394 = lean::cnstr_get(x_391, 1);
x_396 = lean::cnstr_get(x_391, 2);
if (lean::is_exclusive(x_391)) {
 x_398 = x_391;
} else {
 lean::inc(x_392);
 lean::inc(x_394);
 lean::inc(x_396);
 lean::dec(x_391);
 x_398 = lean::box(0);
}
x_399 = lean::apply_1(x_244, x_392);
x_400 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_398)) {
 x_401 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_401 = x_398;
}
lean::cnstr_set(x_401, 0, x_399);
lean::cnstr_set(x_401, 1, x_394);
lean::cnstr_set(x_401, 2, x_400);
x_402 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_401);
x_403 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_246, x_402);
if (lean::obj_tag(x_403) == 0)
{
obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_407 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_403);
x_408 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_407);
x_409 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_408);
x_410 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_409);
x_411 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_410);
x_412 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_411);
return x_412;
}
else
{
obj* x_413; uint8 x_415; 
x_413 = lean::cnstr_get(x_403, 0);
lean::inc(x_413);
x_415 = lean::cnstr_get_scalar<uint8>(x_403, sizeof(void*)*1);
x_240 = x_403;
x_241 = x_413;
x_242 = x_415;
goto lbl_243;
}
}
else
{
obj* x_417; uint8 x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; 
lean::dec(x_244);
x_417 = lean::cnstr_get(x_391, 0);
x_419 = lean::cnstr_get_scalar<uint8>(x_391, sizeof(void*)*1);
if (lean::is_exclusive(x_391)) {
 x_420 = x_391;
} else {
 lean::inc(x_417);
 lean::dec(x_391);
 x_420 = lean::box(0);
}
if (lean::is_scalar(x_420)) {
 x_421 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_421 = x_420;
}
lean::cnstr_set(x_421, 0, x_417);
lean::cnstr_set_scalar(x_421, sizeof(void*)*1, x_419);
x_422 = x_421;
x_423 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_246, x_422);
if (lean::obj_tag(x_423) == 0)
{
obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_427 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_423);
x_428 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_104, x_427);
x_429 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_100, x_428);
x_430 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_429);
x_431 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_430);
x_432 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_431);
return x_432;
}
else
{
obj* x_433; uint8 x_435; 
x_433 = lean::cnstr_get(x_423, 0);
lean::inc(x_433);
x_435 = lean::cnstr_get_scalar<uint8>(x_423, sizeof(void*)*1);
x_240 = x_423;
x_241 = x_433;
x_242 = x_435;
goto lbl_243;
}
}
}
}
}
}
}
lbl_31:
{
obj* x_436; 
x_436 = l_lean_ir_parse__usize(x_29);
if (lean::obj_tag(x_436) == 0)
{
obj* x_437; obj* x_439; obj* x_441; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; 
x_437 = lean::cnstr_get(x_436, 0);
x_439 = lean::cnstr_get(x_436, 1);
x_441 = lean::cnstr_get(x_436, 2);
if (lean::is_exclusive(x_436)) {
 x_443 = x_436;
} else {
 lean::inc(x_437);
 lean::inc(x_439);
 lean::inc(x_441);
 lean::dec(x_436);
 x_443 = lean::box(0);
}
x_444 = lean::apply_1(x_28, x_437);
x_445 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_443)) {
 x_446 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_446 = x_443;
}
lean::cnstr_set(x_446, 0, x_444);
lean::cnstr_set(x_446, 1, x_439);
lean::cnstr_set(x_446, 2, x_445);
x_447 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_441, x_446);
x_448 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_447);
x_26 = x_448;
goto lbl_27;
}
else
{
obj* x_450; uint8 x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; 
lean::dec(x_28);
x_450 = lean::cnstr_get(x_436, 0);
x_452 = lean::cnstr_get_scalar<uint8>(x_436, sizeof(void*)*1);
if (lean::is_exclusive(x_436)) {
 x_453 = x_436;
} else {
 lean::inc(x_450);
 lean::dec(x_436);
 x_453 = lean::box(0);
}
if (lean::is_scalar(x_453)) {
 x_454 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_454 = x_453;
}
lean::cnstr_set(x_454, 0, x_450);
lean::cnstr_set_scalar(x_454, sizeof(void*)*1, x_452);
x_455 = x_454;
x_456 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_455);
x_26 = x_456;
goto lbl_27;
}
}
}
else
{
obj* x_459; uint8 x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; 
lean::dec(x_0);
lean::dec(x_12);
x_459 = lean::cnstr_get(x_20, 0);
x_461 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_462 = x_20;
} else {
 lean::inc(x_459);
 lean::dec(x_20);
 x_462 = lean::box(0);
}
if (lean::is_scalar(x_462)) {
 x_463 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_463 = x_462;
}
lean::cnstr_set(x_463, 0, x_459);
lean::cnstr_set_scalar(x_463, sizeof(void*)*1, x_461);
x_464 = x_463;
x_465 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_464);
x_466 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_465);
return x_466;
}
}
else
{
obj* x_468; uint8 x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
lean::dec(x_0);
x_468 = lean::cnstr_get(x_11, 0);
x_470 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_471 = x_11;
} else {
 lean::inc(x_468);
 lean::dec(x_11);
 x_471 = lean::box(0);
}
if (lean::is_scalar(x_471)) {
 x_472 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_472 = x_471;
}
lean::cnstr_set(x_472, 0, x_468);
lean::cnstr_set_scalar(x_472, sizeof(void*)*1, x_470);
x_473 = x_472;
x_474 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_473);
return x_474;
}
}
else
{
obj* x_476; uint8 x_478; obj* x_479; obj* x_480; obj* x_481; 
lean::dec(x_0);
x_476 = lean::cnstr_get(x_3, 0);
x_478 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_479 = x_3;
} else {
 lean::inc(x_476);
 lean::dec(x_3);
 x_479 = lean::box(0);
}
if (lean::is_scalar(x_479)) {
 x_480 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_480 = x_479;
}
lean::cnstr_set(x_480, 0, x_476);
lean::cnstr_set_scalar(x_480, sizeof(void*)*1, x_478);
x_481 = x_480;
return x_481;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_15 = l_lean_ir_parse__untyped__assignment___closed__7;
lean::inc(x_4);
x_17 = l_lean_ir_keyword(x_15, x_4);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_20; obj* x_23; 
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_ir_parse__fnid(x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_24 = lean::cnstr_get(x_23, 0);
x_26 = lean::cnstr_get(x_23, 1);
x_28 = lean::cnstr_get(x_23, 2);
if (lean::is_exclusive(x_23)) {
 x_30 = x_23;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_23);
 x_30 = lean::box(0);
}
lean::inc(x_0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__6), 3, 2);
lean::closure_set(x_32, 0, x_0);
lean::closure_set(x_32, 1, x_24);
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_30)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_30;
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
obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_50 = lean::cnstr_get(x_23, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_exclusive(x_23)) {
 x_53 = x_23;
} else {
 lean::inc(x_50);
 lean::dec(x_23);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_59; obj* x_61; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_56, 2);
lean::inc(x_61);
lean::dec(x_56);
x_11 = x_57;
x_12 = x_59;
x_13 = x_61;
goto lbl_14;
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_56, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_exclusive(x_56)) {
 x_67 = x_56;
} else {
 lean::inc(x_64);
 lean::dec(x_56);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_9 = x_69;
goto lbl_10;
}
}
}
else
{
obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; 
x_70 = lean::cnstr_get(x_17, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 x_73 = x_17;
} else {
 lean::inc(x_70);
 lean::dec(x_17);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_9 = x_75;
goto lbl_10;
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_78; 
lean::dec(x_4);
lean::dec(x_0);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_78;
}
else
{
obj* x_79; uint8 x_81; obj* x_82; obj* x_83; uint8 x_84; 
x_79 = lean::cnstr_get(x_9, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_81 == 0)
{
obj* x_87; obj* x_89; 
lean::dec(x_9);
x_87 = l_lean_ir_parse__untyped__assignment___closed__6;
lean::inc(x_4);
x_89 = l_lean_ir_keyword(x_87, x_4);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_92; obj* x_95; 
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 2);
lean::inc(x_92);
lean::dec(x_89);
x_95 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(x_90);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_96 = lean::cnstr_get(x_95, 0);
x_98 = lean::cnstr_get(x_95, 1);
x_100 = lean::cnstr_get(x_95, 2);
if (lean::is_exclusive(x_95)) {
 x_102 = x_95;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_95);
 x_102 = lean::box(0);
}
lean::inc(x_0);
x_104 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_104, 0, x_0);
lean::cnstr_set(x_104, 1, x_96);
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_102)) {
 x_106 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_106 = x_102;
}
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_98);
lean::cnstr_set(x_106, 2, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_111; obj* x_112; 
lean::dec(x_4);
lean::dec(x_0);
x_111 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_108);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_111);
return x_112;
}
else
{
obj* x_113; uint8 x_115; 
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<uint8>(x_108, sizeof(void*)*1);
x_82 = x_108;
x_83 = x_113;
x_84 = x_115;
goto lbl_85;
}
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_116 = lean::cnstr_get(x_95, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
if (lean::is_exclusive(x_95)) {
 x_119 = x_95;
} else {
 lean::inc(x_116);
 lean::dec(x_95);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set_scalar(x_120, sizeof(void*)*1, x_118);
x_121 = x_120;
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_125; obj* x_126; 
lean::dec(x_4);
lean::dec(x_0);
x_125 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_122);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_125);
return x_126;
}
else
{
obj* x_127; uint8 x_129; 
x_127 = lean::cnstr_get(x_122, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_122, sizeof(void*)*1);
x_82 = x_122;
x_83 = x_127;
x_84 = x_129;
goto lbl_85;
}
}
}
else
{
obj* x_130; uint8 x_132; obj* x_133; obj* x_135; obj* x_136; 
x_130 = lean::cnstr_get(x_89, 0);
x_132 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
if (lean::is_exclusive(x_89)) {
 x_133 = x_89;
} else {
 lean::inc(x_130);
 lean::dec(x_89);
 x_133 = lean::box(0);
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
x_82 = x_136;
x_83 = x_130;
x_84 = x_132;
goto lbl_85;
}
}
else
{
obj* x_140; 
lean::dec(x_79);
lean::dec(x_4);
lean::dec(x_0);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_140;
}
lbl_85:
{
obj* x_141; obj* x_142; uint8 x_143; obj* x_145; obj* x_146; obj* x_147; 
if (x_84 == 0)
{
obj* x_150; obj* x_152; 
lean::dec(x_82);
x_150 = l_lean_ir_parse__untyped__assignment___closed__5;
lean::inc(x_4);
x_152 = l_lean_ir_keyword(x_150, x_4);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_155; obj* x_158; 
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 2);
lean::inc(x_155);
lean::dec(x_152);
x_158 = l_lean_ir_parse__var(x_153);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_159 = lean::cnstr_get(x_158, 0);
x_161 = lean::cnstr_get(x_158, 1);
x_163 = lean::cnstr_get(x_158, 2);
if (lean::is_exclusive(x_158)) {
 x_165 = x_158;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_158);
 x_165 = lean::box(0);
}
lean::inc(x_0);
x_167 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__5___boxed), 3, 2);
lean::closure_set(x_167, 0, x_0);
lean::closure_set(x_167, 1, x_159);
x_168 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_165)) {
 x_169 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_169 = x_165;
}
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set(x_169, 1, x_161);
lean::cnstr_set(x_169, 2, x_168);
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_169);
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_155, x_170);
if (lean::obj_tag(x_171) == 0)
{
obj* x_172; obj* x_174; obj* x_176; 
x_172 = lean::cnstr_get(x_171, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_171, 2);
lean::inc(x_176);
lean::dec(x_171);
x_145 = x_172;
x_146 = x_174;
x_147 = x_176;
goto lbl_148;
}
else
{
obj* x_179; uint8 x_181; obj* x_182; obj* x_184; obj* x_185; 
x_179 = lean::cnstr_get(x_171, 0);
x_181 = lean::cnstr_get_scalar<uint8>(x_171, sizeof(void*)*1);
if (lean::is_exclusive(x_171)) {
 x_182 = x_171;
} else {
 lean::inc(x_179);
 lean::dec(x_171);
 x_182 = lean::box(0);
}
lean::inc(x_179);
if (lean::is_scalar(x_182)) {
 x_184 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_184 = x_182;
}
lean::cnstr_set(x_184, 0, x_179);
lean::cnstr_set_scalar(x_184, sizeof(void*)*1, x_181);
x_185 = x_184;
x_141 = x_185;
x_142 = x_179;
x_143 = x_181;
goto lbl_144;
}
}
else
{
obj* x_186; uint8 x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_186 = lean::cnstr_get(x_158, 0);
x_188 = lean::cnstr_get_scalar<uint8>(x_158, sizeof(void*)*1);
if (lean::is_exclusive(x_158)) {
 x_189 = x_158;
} else {
 lean::inc(x_186);
 lean::dec(x_158);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_186);
lean::cnstr_set_scalar(x_190, sizeof(void*)*1, x_188);
x_191 = x_190;
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_155, x_191);
if (lean::obj_tag(x_192) == 0)
{
obj* x_193; obj* x_195; obj* x_197; 
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 1);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_192, 2);
lean::inc(x_197);
lean::dec(x_192);
x_145 = x_193;
x_146 = x_195;
x_147 = x_197;
goto lbl_148;
}
else
{
obj* x_200; uint8 x_202; obj* x_203; obj* x_205; obj* x_206; 
x_200 = lean::cnstr_get(x_192, 0);
x_202 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*1);
if (lean::is_exclusive(x_192)) {
 x_203 = x_192;
} else {
 lean::inc(x_200);
 lean::dec(x_192);
 x_203 = lean::box(0);
}
lean::inc(x_200);
if (lean::is_scalar(x_203)) {
 x_205 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_205 = x_203;
}
lean::cnstr_set(x_205, 0, x_200);
lean::cnstr_set_scalar(x_205, sizeof(void*)*1, x_202);
x_206 = x_205;
x_141 = x_206;
x_142 = x_200;
x_143 = x_202;
goto lbl_144;
}
}
}
else
{
obj* x_207; uint8 x_209; obj* x_210; obj* x_212; obj* x_213; 
x_207 = lean::cnstr_get(x_152, 0);
x_209 = lean::cnstr_get_scalar<uint8>(x_152, sizeof(void*)*1);
if (lean::is_exclusive(x_152)) {
 x_210 = x_152;
} else {
 lean::inc(x_207);
 lean::dec(x_152);
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
x_141 = x_213;
x_142 = x_207;
x_143 = x_209;
goto lbl_144;
}
}
else
{
obj* x_217; obj* x_218; 
lean::dec(x_83);
lean::dec(x_4);
lean::dec(x_0);
x_217 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_82);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_217);
return x_218;
}
lbl_144:
{
obj* x_219; obj* x_220; uint8 x_221; obj* x_223; obj* x_224; obj* x_225; 
if (x_143 == 0)
{
obj* x_228; obj* x_230; 
lean::dec(x_141);
x_228 = l_lean_ir_parse__untyped__assignment___closed__4;
lean::inc(x_4);
x_230 = l_lean_ir_keyword(x_228, x_4);
if (lean::obj_tag(x_230) == 0)
{
obj* x_231; obj* x_233; obj* x_236; 
x_231 = lean::cnstr_get(x_230, 1);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_230, 2);
lean::inc(x_233);
lean::dec(x_230);
x_236 = l_lean_ir_parse__fnid(x_231);
if (lean::obj_tag(x_236) == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_237 = lean::cnstr_get(x_236, 0);
x_239 = lean::cnstr_get(x_236, 1);
x_241 = lean::cnstr_get(x_236, 2);
if (lean::is_exclusive(x_236)) {
 x_243 = x_236;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_236);
 x_243 = lean::box(0);
}
lean::inc(x_0);
x_245 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__4), 3, 2);
lean::closure_set(x_245, 0, x_0);
lean::closure_set(x_245, 1, x_237);
x_246 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_243)) {
 x_247 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_247 = x_243;
}
lean::cnstr_set(x_247, 0, x_245);
lean::cnstr_set(x_247, 1, x_239);
lean::cnstr_set(x_247, 2, x_246);
x_248 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_247);
x_249 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_233, x_248);
if (lean::obj_tag(x_249) == 0)
{
obj* x_250; obj* x_252; obj* x_254; 
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_249, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_249, 2);
lean::inc(x_254);
lean::dec(x_249);
x_223 = x_250;
x_224 = x_252;
x_225 = x_254;
goto lbl_226;
}
else
{
obj* x_257; uint8 x_259; obj* x_260; obj* x_262; obj* x_263; 
x_257 = lean::cnstr_get(x_249, 0);
x_259 = lean::cnstr_get_scalar<uint8>(x_249, sizeof(void*)*1);
if (lean::is_exclusive(x_249)) {
 x_260 = x_249;
} else {
 lean::inc(x_257);
 lean::dec(x_249);
 x_260 = lean::box(0);
}
lean::inc(x_257);
if (lean::is_scalar(x_260)) {
 x_262 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_262 = x_260;
}
lean::cnstr_set(x_262, 0, x_257);
lean::cnstr_set_scalar(x_262, sizeof(void*)*1, x_259);
x_263 = x_262;
x_219 = x_263;
x_220 = x_257;
x_221 = x_259;
goto lbl_222;
}
}
else
{
obj* x_264; uint8 x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; 
x_264 = lean::cnstr_get(x_236, 0);
x_266 = lean::cnstr_get_scalar<uint8>(x_236, sizeof(void*)*1);
if (lean::is_exclusive(x_236)) {
 x_267 = x_236;
} else {
 lean::inc(x_264);
 lean::dec(x_236);
 x_267 = lean::box(0);
}
if (lean::is_scalar(x_267)) {
 x_268 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_268 = x_267;
}
lean::cnstr_set(x_268, 0, x_264);
lean::cnstr_set_scalar(x_268, sizeof(void*)*1, x_266);
x_269 = x_268;
x_270 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_233, x_269);
if (lean::obj_tag(x_270) == 0)
{
obj* x_271; obj* x_273; obj* x_275; 
x_271 = lean::cnstr_get(x_270, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_270, 1);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_270, 2);
lean::inc(x_275);
lean::dec(x_270);
x_223 = x_271;
x_224 = x_273;
x_225 = x_275;
goto lbl_226;
}
else
{
obj* x_278; uint8 x_280; obj* x_281; obj* x_283; obj* x_284; 
x_278 = lean::cnstr_get(x_270, 0);
x_280 = lean::cnstr_get_scalar<uint8>(x_270, sizeof(void*)*1);
if (lean::is_exclusive(x_270)) {
 x_281 = x_270;
} else {
 lean::inc(x_278);
 lean::dec(x_270);
 x_281 = lean::box(0);
}
lean::inc(x_278);
if (lean::is_scalar(x_281)) {
 x_283 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_283 = x_281;
}
lean::cnstr_set(x_283, 0, x_278);
lean::cnstr_set_scalar(x_283, sizeof(void*)*1, x_280);
x_284 = x_283;
x_219 = x_284;
x_220 = x_278;
x_221 = x_280;
goto lbl_222;
}
}
}
else
{
obj* x_285; uint8 x_287; obj* x_288; obj* x_290; obj* x_291; 
x_285 = lean::cnstr_get(x_230, 0);
x_287 = lean::cnstr_get_scalar<uint8>(x_230, sizeof(void*)*1);
if (lean::is_exclusive(x_230)) {
 x_288 = x_230;
} else {
 lean::inc(x_285);
 lean::dec(x_230);
 x_288 = lean::box(0);
}
lean::inc(x_285);
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_285);
lean::cnstr_set_scalar(x_290, sizeof(void*)*1, x_287);
x_291 = x_290;
x_219 = x_291;
x_220 = x_285;
x_221 = x_287;
goto lbl_222;
}
}
else
{
obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_142);
lean::dec(x_4);
lean::dec(x_0);
x_295 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_141);
x_296 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_295);
x_297 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_296);
return x_297;
}
lbl_222:
{
obj* x_298; obj* x_299; uint8 x_300; obj* x_302; obj* x_303; obj* x_304; obj* x_306; obj* x_307; obj* x_308; 
if (x_221 == 0)
{
obj* x_311; obj* x_313; 
lean::dec(x_219);
x_311 = l_lean_ir_parse__untyped__assignment___closed__3;
lean::inc(x_4);
x_313 = l_lean_ir_keyword(x_311, x_4);
if (lean::obj_tag(x_313) == 0)
{
obj* x_314; obj* x_316; obj* x_319; 
x_314 = lean::cnstr_get(x_313, 1);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_313, 2);
lean::inc(x_316);
lean::dec(x_313);
x_319 = l_lean_ir_parse__uint16(x_314);
if (lean::obj_tag(x_319) == 0)
{
obj* x_320; obj* x_322; obj* x_324; obj* x_326; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; 
x_320 = lean::cnstr_get(x_319, 0);
x_322 = lean::cnstr_get(x_319, 1);
x_324 = lean::cnstr_get(x_319, 2);
if (lean::is_exclusive(x_319)) {
 x_326 = x_319;
} else {
 lean::inc(x_320);
 lean::inc(x_322);
 lean::inc(x_324);
 lean::dec(x_319);
 x_326 = lean::box(0);
}
lean::inc(x_0);
x_328 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__3___boxed), 4, 2);
lean::closure_set(x_328, 0, x_0);
lean::closure_set(x_328, 1, x_320);
x_329 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_326)) {
 x_330 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_330 = x_326;
}
lean::cnstr_set(x_330, 0, x_328);
lean::cnstr_set(x_330, 1, x_322);
lean::cnstr_set(x_330, 2, x_329);
x_331 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_324, x_330);
x_332 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_316, x_331);
if (lean::obj_tag(x_332) == 0)
{
obj* x_333; obj* x_335; obj* x_337; 
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_332, 2);
lean::inc(x_337);
lean::dec(x_332);
x_306 = x_333;
x_307 = x_335;
x_308 = x_337;
goto lbl_309;
}
else
{
obj* x_340; uint8 x_342; obj* x_343; obj* x_345; obj* x_346; 
x_340 = lean::cnstr_get(x_332, 0);
x_342 = lean::cnstr_get_scalar<uint8>(x_332, sizeof(void*)*1);
if (lean::is_exclusive(x_332)) {
 x_343 = x_332;
} else {
 lean::inc(x_340);
 lean::dec(x_332);
 x_343 = lean::box(0);
}
lean::inc(x_340);
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_340);
lean::cnstr_set_scalar(x_345, sizeof(void*)*1, x_342);
x_346 = x_345;
x_298 = x_346;
x_299 = x_340;
x_300 = x_342;
goto lbl_301;
}
}
else
{
obj* x_347; uint8 x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; 
x_347 = lean::cnstr_get(x_319, 0);
x_349 = lean::cnstr_get_scalar<uint8>(x_319, sizeof(void*)*1);
if (lean::is_exclusive(x_319)) {
 x_350 = x_319;
} else {
 lean::inc(x_347);
 lean::dec(x_319);
 x_350 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_347);
lean::cnstr_set_scalar(x_351, sizeof(void*)*1, x_349);
x_352 = x_351;
x_353 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_316, x_352);
if (lean::obj_tag(x_353) == 0)
{
obj* x_354; obj* x_356; obj* x_358; 
x_354 = lean::cnstr_get(x_353, 0);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_353, 1);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_353, 2);
lean::inc(x_358);
lean::dec(x_353);
x_306 = x_354;
x_307 = x_356;
x_308 = x_358;
goto lbl_309;
}
else
{
obj* x_361; uint8 x_363; obj* x_364; obj* x_366; obj* x_367; 
x_361 = lean::cnstr_get(x_353, 0);
x_363 = lean::cnstr_get_scalar<uint8>(x_353, sizeof(void*)*1);
if (lean::is_exclusive(x_353)) {
 x_364 = x_353;
} else {
 lean::inc(x_361);
 lean::dec(x_353);
 x_364 = lean::box(0);
}
lean::inc(x_361);
if (lean::is_scalar(x_364)) {
 x_366 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_366 = x_364;
}
lean::cnstr_set(x_366, 0, x_361);
lean::cnstr_set_scalar(x_366, sizeof(void*)*1, x_363);
x_367 = x_366;
x_298 = x_367;
x_299 = x_361;
x_300 = x_363;
goto lbl_301;
}
}
}
else
{
obj* x_368; uint8 x_370; obj* x_371; obj* x_373; obj* x_374; 
x_368 = lean::cnstr_get(x_313, 0);
x_370 = lean::cnstr_get_scalar<uint8>(x_313, sizeof(void*)*1);
if (lean::is_exclusive(x_313)) {
 x_371 = x_313;
} else {
 lean::inc(x_368);
 lean::dec(x_313);
 x_371 = lean::box(0);
}
lean::inc(x_368);
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*1, x_370);
x_374 = x_373;
x_298 = x_374;
x_299 = x_368;
x_300 = x_370;
goto lbl_301;
}
}
else
{
obj* x_378; obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_220);
x_378 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_219);
x_379 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_378);
x_380 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_379);
x_381 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_380);
return x_381;
}
lbl_301:
{
obj* x_382; obj* x_383; uint8 x_384; obj* x_386; obj* x_387; obj* x_388; 
if (x_300 == 0)
{
obj* x_391; obj* x_393; 
lean::dec(x_298);
x_391 = l_lean_ir_parse__untyped__assignment___closed__2;
lean::inc(x_4);
x_393 = l_lean_ir_keyword(x_391, x_4);
if (lean::obj_tag(x_393) == 0)
{
obj* x_394; obj* x_396; obj* x_399; 
x_394 = lean::cnstr_get(x_393, 1);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_393, 2);
lean::inc(x_396);
lean::dec(x_393);
x_399 = l_lean_ir_parse__var(x_394);
if (lean::obj_tag(x_399) == 0)
{
obj* x_400; obj* x_402; obj* x_404; obj* x_406; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; 
x_400 = lean::cnstr_get(x_399, 0);
x_402 = lean::cnstr_get(x_399, 1);
x_404 = lean::cnstr_get(x_399, 2);
if (lean::is_exclusive(x_399)) {
 x_406 = x_399;
} else {
 lean::inc(x_400);
 lean::inc(x_402);
 lean::inc(x_404);
 lean::dec(x_399);
 x_406 = lean::box(0);
}
lean::inc(x_0);
x_408 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__2), 3, 2);
lean::closure_set(x_408, 0, x_0);
lean::closure_set(x_408, 1, x_400);
x_409 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_406)) {
 x_410 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_410 = x_406;
}
lean::cnstr_set(x_410, 0, x_408);
lean::cnstr_set(x_410, 1, x_402);
lean::cnstr_set(x_410, 2, x_409);
x_411 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_404, x_410);
x_412 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_411);
if (lean::obj_tag(x_412) == 0)
{
obj* x_413; obj* x_415; obj* x_417; 
x_413 = lean::cnstr_get(x_412, 0);
lean::inc(x_413);
x_415 = lean::cnstr_get(x_412, 1);
lean::inc(x_415);
x_417 = lean::cnstr_get(x_412, 2);
lean::inc(x_417);
lean::dec(x_412);
x_386 = x_413;
x_387 = x_415;
x_388 = x_417;
goto lbl_389;
}
else
{
obj* x_420; uint8 x_422; obj* x_423; obj* x_425; obj* x_426; 
x_420 = lean::cnstr_get(x_412, 0);
x_422 = lean::cnstr_get_scalar<uint8>(x_412, sizeof(void*)*1);
if (lean::is_exclusive(x_412)) {
 x_423 = x_412;
} else {
 lean::inc(x_420);
 lean::dec(x_412);
 x_423 = lean::box(0);
}
lean::inc(x_420);
if (lean::is_scalar(x_423)) {
 x_425 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_425 = x_423;
}
lean::cnstr_set(x_425, 0, x_420);
lean::cnstr_set_scalar(x_425, sizeof(void*)*1, x_422);
x_426 = x_425;
x_382 = x_426;
x_383 = x_420;
x_384 = x_422;
goto lbl_385;
}
}
else
{
obj* x_427; uint8 x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; 
x_427 = lean::cnstr_get(x_399, 0);
x_429 = lean::cnstr_get_scalar<uint8>(x_399, sizeof(void*)*1);
if (lean::is_exclusive(x_399)) {
 x_430 = x_399;
} else {
 lean::inc(x_427);
 lean::dec(x_399);
 x_430 = lean::box(0);
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_427);
lean::cnstr_set_scalar(x_431, sizeof(void*)*1, x_429);
x_432 = x_431;
x_433 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_432);
if (lean::obj_tag(x_433) == 0)
{
obj* x_434; obj* x_436; obj* x_438; 
x_434 = lean::cnstr_get(x_433, 0);
lean::inc(x_434);
x_436 = lean::cnstr_get(x_433, 1);
lean::inc(x_436);
x_438 = lean::cnstr_get(x_433, 2);
lean::inc(x_438);
lean::dec(x_433);
x_386 = x_434;
x_387 = x_436;
x_388 = x_438;
goto lbl_389;
}
else
{
obj* x_441; uint8 x_443; obj* x_444; obj* x_446; obj* x_447; 
x_441 = lean::cnstr_get(x_433, 0);
x_443 = lean::cnstr_get_scalar<uint8>(x_433, sizeof(void*)*1);
if (lean::is_exclusive(x_433)) {
 x_444 = x_433;
} else {
 lean::inc(x_441);
 lean::dec(x_433);
 x_444 = lean::box(0);
}
lean::inc(x_441);
if (lean::is_scalar(x_444)) {
 x_446 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_446 = x_444;
}
lean::cnstr_set(x_446, 0, x_441);
lean::cnstr_set_scalar(x_446, sizeof(void*)*1, x_443);
x_447 = x_446;
x_382 = x_447;
x_383 = x_441;
x_384 = x_443;
goto lbl_385;
}
}
}
else
{
obj* x_448; uint8 x_450; obj* x_451; obj* x_453; obj* x_454; 
x_448 = lean::cnstr_get(x_393, 0);
x_450 = lean::cnstr_get_scalar<uint8>(x_393, sizeof(void*)*1);
if (lean::is_exclusive(x_393)) {
 x_451 = x_393;
} else {
 lean::inc(x_448);
 lean::dec(x_393);
 x_451 = lean::box(0);
}
lean::inc(x_448);
if (lean::is_scalar(x_451)) {
 x_453 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_453 = x_451;
}
lean::cnstr_set(x_453, 0, x_448);
lean::cnstr_set_scalar(x_453, sizeof(void*)*1, x_450);
x_454 = x_453;
x_382 = x_454;
x_383 = x_448;
x_384 = x_450;
goto lbl_385;
}
}
else
{
obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_299);
x_458 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_298);
x_459 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_458);
x_460 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_459);
x_461 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_460);
x_462 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_461);
return x_462;
}
lbl_385:
{
obj* x_463; obj* x_464; obj* x_465; obj* x_467; obj* x_468; obj* x_469; 
if (x_384 == 0)
{
obj* x_472; obj* x_473; 
lean::dec(x_382);
x_472 = l_lean_ir_parse__untyped__assignment___closed__1;
x_473 = l_lean_ir_keyword(x_472, x_4);
if (lean::obj_tag(x_473) == 0)
{
obj* x_474; obj* x_476; obj* x_479; obj* x_480; obj* x_481; 
x_474 = lean::cnstr_get(x_473, 1);
lean::inc(x_474);
x_476 = lean::cnstr_get(x_473, 2);
lean::inc(x_476);
lean::dec(x_473);
x_479 = l_lean_ir_parse__typed__assignment___closed__2;
x_480 = l_lean_ir_str2type;
x_481 = l_lean_ir_parse__key2val___main___rarg(x_479, x_480, x_474);
if (lean::obj_tag(x_481) == 0)
{
obj* x_482; obj* x_484; obj* x_486; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; 
x_482 = lean::cnstr_get(x_481, 0);
x_484 = lean::cnstr_get(x_481, 1);
x_486 = lean::cnstr_get(x_481, 2);
if (lean::is_exclusive(x_481)) {
 x_488 = x_481;
} else {
 lean::inc(x_482);
 lean::inc(x_484);
 lean::inc(x_486);
 lean::dec(x_481);
 x_488 = lean::box(0);
}
x_489 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__1___boxed), 4, 2);
lean::closure_set(x_489, 0, x_0);
lean::closure_set(x_489, 1, x_482);
x_490 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_488)) {
 x_491 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_491 = x_488;
}
lean::cnstr_set(x_491, 0, x_489);
lean::cnstr_set(x_491, 1, x_484);
lean::cnstr_set(x_491, 2, x_490);
x_492 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_486, x_491);
x_493 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_476, x_492);
if (lean::obj_tag(x_493) == 0)
{
obj* x_494; obj* x_496; obj* x_498; 
x_494 = lean::cnstr_get(x_493, 0);
lean::inc(x_494);
x_496 = lean::cnstr_get(x_493, 1);
lean::inc(x_496);
x_498 = lean::cnstr_get(x_493, 2);
lean::inc(x_498);
lean::dec(x_493);
x_467 = x_494;
x_468 = x_496;
x_469 = x_498;
goto lbl_470;
}
else
{
obj* x_501; uint8 x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; 
x_501 = lean::cnstr_get(x_493, 0);
x_503 = lean::cnstr_get_scalar<uint8>(x_493, sizeof(void*)*1);
if (lean::is_exclusive(x_493)) {
 x_504 = x_493;
} else {
 lean::inc(x_501);
 lean::dec(x_493);
 x_504 = lean::box(0);
}
if (lean::is_scalar(x_504)) {
 x_505 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_505 = x_504;
}
lean::cnstr_set(x_505, 0, x_501);
lean::cnstr_set_scalar(x_505, sizeof(void*)*1, x_503);
x_506 = x_505;
x_507 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_506);
x_508 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_507);
x_509 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_508);
x_510 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_509);
x_511 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_510);
x_512 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_511);
x_513 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_512);
return x_513;
}
}
else
{
obj* x_515; uint8 x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; 
lean::dec(x_0);
x_515 = lean::cnstr_get(x_481, 0);
x_517 = lean::cnstr_get_scalar<uint8>(x_481, sizeof(void*)*1);
if (lean::is_exclusive(x_481)) {
 x_518 = x_481;
} else {
 lean::inc(x_515);
 lean::dec(x_481);
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
x_521 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_476, x_520);
if (lean::obj_tag(x_521) == 0)
{
obj* x_522; obj* x_524; obj* x_526; 
x_522 = lean::cnstr_get(x_521, 0);
lean::inc(x_522);
x_524 = lean::cnstr_get(x_521, 1);
lean::inc(x_524);
x_526 = lean::cnstr_get(x_521, 2);
lean::inc(x_526);
lean::dec(x_521);
x_467 = x_522;
x_468 = x_524;
x_469 = x_526;
goto lbl_470;
}
else
{
obj* x_529; uint8 x_531; obj* x_532; obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; 
x_529 = lean::cnstr_get(x_521, 0);
x_531 = lean::cnstr_get_scalar<uint8>(x_521, sizeof(void*)*1);
if (lean::is_exclusive(x_521)) {
 x_532 = x_521;
} else {
 lean::inc(x_529);
 lean::dec(x_521);
 x_532 = lean::box(0);
}
if (lean::is_scalar(x_532)) {
 x_533 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_533 = x_532;
}
lean::cnstr_set(x_533, 0, x_529);
lean::cnstr_set_scalar(x_533, sizeof(void*)*1, x_531);
x_534 = x_533;
x_535 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_534);
x_536 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_535);
x_537 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_536);
x_538 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_537);
x_539 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_538);
x_540 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_539);
x_541 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_540);
return x_541;
}
}
}
else
{
obj* x_543; uint8 x_545; obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; 
lean::dec(x_0);
x_543 = lean::cnstr_get(x_473, 0);
x_545 = lean::cnstr_get_scalar<uint8>(x_473, sizeof(void*)*1);
if (lean::is_exclusive(x_473)) {
 x_546 = x_473;
} else {
 lean::inc(x_543);
 lean::dec(x_473);
 x_546 = lean::box(0);
}
if (lean::is_scalar(x_546)) {
 x_547 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_547 = x_546;
}
lean::cnstr_set(x_547, 0, x_543);
lean::cnstr_set_scalar(x_547, sizeof(void*)*1, x_545);
x_548 = x_547;
x_549 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_548);
x_550 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_549);
x_551 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_550);
x_552 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_551);
x_553 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_552);
x_554 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_553);
x_555 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_554);
return x_555;
}
}
else
{
obj* x_559; obj* x_560; obj* x_561; obj* x_562; obj* x_563; obj* x_564; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_383);
x_559 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_382);
x_560 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_559);
x_561 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_560);
x_562 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_561);
x_563 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_562);
x_564 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_563);
return x_564;
}
lbl_466:
{
obj* x_565; 
x_565 = l_lean_ir_parse__var(x_464);
if (lean::obj_tag(x_565) == 0)
{
obj* x_566; obj* x_568; obj* x_570; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; 
x_566 = lean::cnstr_get(x_565, 0);
x_568 = lean::cnstr_get(x_565, 1);
x_570 = lean::cnstr_get(x_565, 2);
if (lean::is_exclusive(x_565)) {
 x_572 = x_565;
} else {
 lean::inc(x_566);
 lean::inc(x_568);
 lean::inc(x_570);
 lean::dec(x_565);
 x_572 = lean::box(0);
}
x_573 = lean::apply_1(x_463, x_566);
x_574 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_572)) {
 x_575 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_575 = x_572;
}
lean::cnstr_set(x_575, 0, x_573);
lean::cnstr_set(x_575, 1, x_568);
lean::cnstr_set(x_575, 2, x_574);
x_576 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_570, x_575);
x_577 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_465, x_576);
x_578 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_577);
x_579 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_578);
x_580 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_579);
x_581 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_580);
x_582 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_581);
x_583 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_582);
x_584 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_583);
return x_584;
}
else
{
obj* x_586; uint8 x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; 
lean::dec(x_463);
x_586 = lean::cnstr_get(x_565, 0);
x_588 = lean::cnstr_get_scalar<uint8>(x_565, sizeof(void*)*1);
if (lean::is_exclusive(x_565)) {
 x_589 = x_565;
} else {
 lean::inc(x_586);
 lean::dec(x_565);
 x_589 = lean::box(0);
}
if (lean::is_scalar(x_589)) {
 x_590 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_590 = x_589;
}
lean::cnstr_set(x_590, 0, x_586);
lean::cnstr_set_scalar(x_590, sizeof(void*)*1, x_588);
x_591 = x_590;
x_592 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_465, x_591);
x_593 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_592);
x_594 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_593);
x_595 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_594);
x_596 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_595);
x_597 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_596);
x_598 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_597);
x_599 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_598);
return x_599;
}
}
lbl_470:
{
obj* x_600; 
x_600 = l_lean_ir_parse__var(x_468);
if (lean::obj_tag(x_600) == 0)
{
obj* x_601; obj* x_603; obj* x_605; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; 
x_601 = lean::cnstr_get(x_600, 0);
x_603 = lean::cnstr_get(x_600, 1);
x_605 = lean::cnstr_get(x_600, 2);
if (lean::is_exclusive(x_600)) {
 x_607 = x_600;
} else {
 lean::inc(x_601);
 lean::inc(x_603);
 lean::inc(x_605);
 lean::dec(x_600);
 x_607 = lean::box(0);
}
x_608 = lean::apply_1(x_467, x_601);
x_609 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_607)) {
 x_610 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_610 = x_607;
}
lean::cnstr_set(x_610, 0, x_608);
lean::cnstr_set(x_610, 1, x_603);
lean::cnstr_set(x_610, 2, x_609);
x_611 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_605, x_610);
x_612 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_469, x_611);
if (lean::obj_tag(x_612) == 0)
{
obj* x_613; obj* x_615; obj* x_617; 
x_613 = lean::cnstr_get(x_612, 0);
lean::inc(x_613);
x_615 = lean::cnstr_get(x_612, 1);
lean::inc(x_615);
x_617 = lean::cnstr_get(x_612, 2);
lean::inc(x_617);
lean::dec(x_612);
x_463 = x_613;
x_464 = x_615;
x_465 = x_617;
goto lbl_466;
}
else
{
obj* x_620; uint8 x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; obj* x_631; obj* x_632; 
x_620 = lean::cnstr_get(x_612, 0);
x_622 = lean::cnstr_get_scalar<uint8>(x_612, sizeof(void*)*1);
if (lean::is_exclusive(x_612)) {
 x_623 = x_612;
} else {
 lean::inc(x_620);
 lean::dec(x_612);
 x_623 = lean::box(0);
}
if (lean::is_scalar(x_623)) {
 x_624 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_624 = x_623;
}
lean::cnstr_set(x_624, 0, x_620);
lean::cnstr_set_scalar(x_624, sizeof(void*)*1, x_622);
x_625 = x_624;
x_626 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_625);
x_627 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_626);
x_628 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_627);
x_629 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_628);
x_630 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_629);
x_631 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_630);
x_632 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_631);
return x_632;
}
}
else
{
obj* x_634; uint8 x_636; obj* x_637; obj* x_638; obj* x_639; obj* x_640; 
lean::dec(x_467);
x_634 = lean::cnstr_get(x_600, 0);
x_636 = lean::cnstr_get_scalar<uint8>(x_600, sizeof(void*)*1);
if (lean::is_exclusive(x_600)) {
 x_637 = x_600;
} else {
 lean::inc(x_634);
 lean::dec(x_600);
 x_637 = lean::box(0);
}
if (lean::is_scalar(x_637)) {
 x_638 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_638 = x_637;
}
lean::cnstr_set(x_638, 0, x_634);
lean::cnstr_set_scalar(x_638, sizeof(void*)*1, x_636);
x_639 = x_638;
x_640 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_469, x_639);
if (lean::obj_tag(x_640) == 0)
{
obj* x_641; obj* x_643; obj* x_645; 
x_641 = lean::cnstr_get(x_640, 0);
lean::inc(x_641);
x_643 = lean::cnstr_get(x_640, 1);
lean::inc(x_643);
x_645 = lean::cnstr_get(x_640, 2);
lean::inc(x_645);
lean::dec(x_640);
x_463 = x_641;
x_464 = x_643;
x_465 = x_645;
goto lbl_466;
}
else
{
obj* x_648; uint8 x_650; obj* x_651; obj* x_652; obj* x_653; obj* x_654; obj* x_655; obj* x_656; obj* x_657; obj* x_658; obj* x_659; obj* x_660; 
x_648 = lean::cnstr_get(x_640, 0);
x_650 = lean::cnstr_get_scalar<uint8>(x_640, sizeof(void*)*1);
if (lean::is_exclusive(x_640)) {
 x_651 = x_640;
} else {
 lean::inc(x_648);
 lean::dec(x_640);
 x_651 = lean::box(0);
}
if (lean::is_scalar(x_651)) {
 x_652 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_652 = x_651;
}
lean::cnstr_set(x_652, 0, x_648);
lean::cnstr_set_scalar(x_652, sizeof(void*)*1, x_650);
x_653 = x_652;
x_654 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_383, x_653);
x_655 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_654);
x_656 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_655);
x_657 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_656);
x_658 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_657);
x_659 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_658);
x_660 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_659);
return x_660;
}
}
}
}
lbl_389:
{
obj* x_661; 
x_661 = l_lean_ir_parse__var(x_387);
if (lean::obj_tag(x_661) == 0)
{
obj* x_662; obj* x_664; obj* x_666; obj* x_668; obj* x_669; obj* x_670; obj* x_671; obj* x_672; obj* x_673; 
x_662 = lean::cnstr_get(x_661, 0);
x_664 = lean::cnstr_get(x_661, 1);
x_666 = lean::cnstr_get(x_661, 2);
if (lean::is_exclusive(x_661)) {
 x_668 = x_661;
} else {
 lean::inc(x_662);
 lean::inc(x_664);
 lean::inc(x_666);
 lean::dec(x_661);
 x_668 = lean::box(0);
}
x_669 = lean::apply_1(x_386, x_662);
x_670 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_668)) {
 x_671 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_671 = x_668;
}
lean::cnstr_set(x_671, 0, x_669);
lean::cnstr_set(x_671, 1, x_664);
lean::cnstr_set(x_671, 2, x_670);
x_672 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_666, x_671);
x_673 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_388, x_672);
if (lean::obj_tag(x_673) == 0)
{
obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; 
lean::dec(x_4);
lean::dec(x_0);
x_676 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_673);
x_677 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_676);
x_678 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_677);
x_679 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_678);
x_680 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_679);
x_681 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_680);
return x_681;
}
else
{
obj* x_682; uint8 x_684; 
x_682 = lean::cnstr_get(x_673, 0);
lean::inc(x_682);
x_684 = lean::cnstr_get_scalar<uint8>(x_673, sizeof(void*)*1);
x_382 = x_673;
x_383 = x_682;
x_384 = x_684;
goto lbl_385;
}
}
else
{
obj* x_686; uint8 x_688; obj* x_689; obj* x_690; obj* x_691; obj* x_692; 
lean::dec(x_386);
x_686 = lean::cnstr_get(x_661, 0);
x_688 = lean::cnstr_get_scalar<uint8>(x_661, sizeof(void*)*1);
if (lean::is_exclusive(x_661)) {
 x_689 = x_661;
} else {
 lean::inc(x_686);
 lean::dec(x_661);
 x_689 = lean::box(0);
}
if (lean::is_scalar(x_689)) {
 x_690 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_690 = x_689;
}
lean::cnstr_set(x_690, 0, x_686);
lean::cnstr_set_scalar(x_690, sizeof(void*)*1, x_688);
x_691 = x_690;
x_692 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_388, x_691);
if (lean::obj_tag(x_692) == 0)
{
obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; 
lean::dec(x_4);
lean::dec(x_0);
x_695 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_299, x_692);
x_696 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_695);
x_697 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_696);
x_698 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_697);
x_699 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_698);
x_700 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_699);
return x_700;
}
else
{
obj* x_701; uint8 x_703; 
x_701 = lean::cnstr_get(x_692, 0);
lean::inc(x_701);
x_703 = lean::cnstr_get_scalar<uint8>(x_692, sizeof(void*)*1);
x_382 = x_692;
x_383 = x_701;
x_384 = x_703;
goto lbl_385;
}
}
}
}
lbl_305:
{
obj* x_704; 
x_704 = l_lean_ir_parse__usize(x_303);
if (lean::obj_tag(x_704) == 0)
{
obj* x_705; obj* x_707; obj* x_709; obj* x_711; obj* x_712; obj* x_713; obj* x_714; obj* x_715; obj* x_716; 
x_705 = lean::cnstr_get(x_704, 0);
x_707 = lean::cnstr_get(x_704, 1);
x_709 = lean::cnstr_get(x_704, 2);
if (lean::is_exclusive(x_704)) {
 x_711 = x_704;
} else {
 lean::inc(x_705);
 lean::inc(x_707);
 lean::inc(x_709);
 lean::dec(x_704);
 x_711 = lean::box(0);
}
x_712 = lean::apply_1(x_302, x_705);
x_713 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_711)) {
 x_714 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_714 = x_711;
}
lean::cnstr_set(x_714, 0, x_712);
lean::cnstr_set(x_714, 1, x_707);
lean::cnstr_set(x_714, 2, x_713);
x_715 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_709, x_714);
x_716 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_304, x_715);
if (lean::obj_tag(x_716) == 0)
{
obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; 
lean::dec(x_4);
lean::dec(x_0);
x_719 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_716);
x_720 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_719);
x_721 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_720);
x_722 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_721);
x_723 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_722);
return x_723;
}
else
{
obj* x_724; uint8 x_726; 
x_724 = lean::cnstr_get(x_716, 0);
lean::inc(x_724);
x_726 = lean::cnstr_get_scalar<uint8>(x_716, sizeof(void*)*1);
x_298 = x_716;
x_299 = x_724;
x_300 = x_726;
goto lbl_301;
}
}
else
{
obj* x_728; uint8 x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; 
lean::dec(x_302);
x_728 = lean::cnstr_get(x_704, 0);
x_730 = lean::cnstr_get_scalar<uint8>(x_704, sizeof(void*)*1);
if (lean::is_exclusive(x_704)) {
 x_731 = x_704;
} else {
 lean::inc(x_728);
 lean::dec(x_704);
 x_731 = lean::box(0);
}
if (lean::is_scalar(x_731)) {
 x_732 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_732 = x_731;
}
lean::cnstr_set(x_732, 0, x_728);
lean::cnstr_set_scalar(x_732, sizeof(void*)*1, x_730);
x_733 = x_732;
x_734 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_304, x_733);
if (lean::obj_tag(x_734) == 0)
{
obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; 
lean::dec(x_4);
lean::dec(x_0);
x_737 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_220, x_734);
x_738 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_737);
x_739 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_738);
x_740 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_739);
x_741 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_740);
return x_741;
}
else
{
obj* x_742; uint8 x_744; 
x_742 = lean::cnstr_get(x_734, 0);
lean::inc(x_742);
x_744 = lean::cnstr_get_scalar<uint8>(x_734, sizeof(void*)*1);
x_298 = x_734;
x_299 = x_742;
x_300 = x_744;
goto lbl_301;
}
}
}
lbl_309:
{
obj* x_745; 
x_745 = l_lean_ir_parse__uint16(x_307);
if (lean::obj_tag(x_745) == 0)
{
obj* x_746; obj* x_748; obj* x_750; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; 
x_746 = lean::cnstr_get(x_745, 0);
x_748 = lean::cnstr_get(x_745, 1);
x_750 = lean::cnstr_get(x_745, 2);
if (lean::is_exclusive(x_745)) {
 x_752 = x_745;
} else {
 lean::inc(x_746);
 lean::inc(x_748);
 lean::inc(x_750);
 lean::dec(x_745);
 x_752 = lean::box(0);
}
x_753 = lean::apply_1(x_306, x_746);
x_754 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_752)) {
 x_755 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_755 = x_752;
}
lean::cnstr_set(x_755, 0, x_753);
lean::cnstr_set(x_755, 1, x_748);
lean::cnstr_set(x_755, 2, x_754);
x_756 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_750, x_755);
x_757 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_756);
if (lean::obj_tag(x_757) == 0)
{
obj* x_758; obj* x_760; obj* x_762; 
x_758 = lean::cnstr_get(x_757, 0);
lean::inc(x_758);
x_760 = lean::cnstr_get(x_757, 1);
lean::inc(x_760);
x_762 = lean::cnstr_get(x_757, 2);
lean::inc(x_762);
lean::dec(x_757);
x_302 = x_758;
x_303 = x_760;
x_304 = x_762;
goto lbl_305;
}
else
{
obj* x_765; uint8 x_767; obj* x_768; obj* x_770; obj* x_771; 
x_765 = lean::cnstr_get(x_757, 0);
x_767 = lean::cnstr_get_scalar<uint8>(x_757, sizeof(void*)*1);
if (lean::is_exclusive(x_757)) {
 x_768 = x_757;
} else {
 lean::inc(x_765);
 lean::dec(x_757);
 x_768 = lean::box(0);
}
lean::inc(x_765);
if (lean::is_scalar(x_768)) {
 x_770 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_770 = x_768;
}
lean::cnstr_set(x_770, 0, x_765);
lean::cnstr_set_scalar(x_770, sizeof(void*)*1, x_767);
x_771 = x_770;
x_298 = x_771;
x_299 = x_765;
x_300 = x_767;
goto lbl_301;
}
}
else
{
obj* x_773; uint8 x_775; obj* x_776; obj* x_777; obj* x_778; obj* x_779; 
lean::dec(x_306);
x_773 = lean::cnstr_get(x_745, 0);
x_775 = lean::cnstr_get_scalar<uint8>(x_745, sizeof(void*)*1);
if (lean::is_exclusive(x_745)) {
 x_776 = x_745;
} else {
 lean::inc(x_773);
 lean::dec(x_745);
 x_776 = lean::box(0);
}
if (lean::is_scalar(x_776)) {
 x_777 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_777 = x_776;
}
lean::cnstr_set(x_777, 0, x_773);
lean::cnstr_set_scalar(x_777, sizeof(void*)*1, x_775);
x_778 = x_777;
x_779 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_778);
if (lean::obj_tag(x_779) == 0)
{
obj* x_780; obj* x_782; obj* x_784; 
x_780 = lean::cnstr_get(x_779, 0);
lean::inc(x_780);
x_782 = lean::cnstr_get(x_779, 1);
lean::inc(x_782);
x_784 = lean::cnstr_get(x_779, 2);
lean::inc(x_784);
lean::dec(x_779);
x_302 = x_780;
x_303 = x_782;
x_304 = x_784;
goto lbl_305;
}
else
{
obj* x_787; uint8 x_789; obj* x_790; obj* x_792; obj* x_793; 
x_787 = lean::cnstr_get(x_779, 0);
x_789 = lean::cnstr_get_scalar<uint8>(x_779, sizeof(void*)*1);
if (lean::is_exclusive(x_779)) {
 x_790 = x_779;
} else {
 lean::inc(x_787);
 lean::dec(x_779);
 x_790 = lean::box(0);
}
lean::inc(x_787);
if (lean::is_scalar(x_790)) {
 x_792 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_792 = x_790;
}
lean::cnstr_set(x_792, 0, x_787);
lean::cnstr_set_scalar(x_792, sizeof(void*)*1, x_789);
x_793 = x_792;
x_298 = x_793;
x_299 = x_787;
x_300 = x_789;
goto lbl_301;
}
}
}
}
lbl_226:
{
obj* x_794; 
x_794 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(x_224);
if (lean::obj_tag(x_794) == 0)
{
obj* x_795; obj* x_797; obj* x_799; obj* x_801; obj* x_802; obj* x_803; obj* x_804; obj* x_805; obj* x_806; 
x_795 = lean::cnstr_get(x_794, 0);
x_797 = lean::cnstr_get(x_794, 1);
x_799 = lean::cnstr_get(x_794, 2);
if (lean::is_exclusive(x_794)) {
 x_801 = x_794;
} else {
 lean::inc(x_795);
 lean::inc(x_797);
 lean::inc(x_799);
 lean::dec(x_794);
 x_801 = lean::box(0);
}
x_802 = lean::apply_1(x_223, x_795);
x_803 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_801)) {
 x_804 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_804 = x_801;
}
lean::cnstr_set(x_804, 0, x_802);
lean::cnstr_set(x_804, 1, x_797);
lean::cnstr_set(x_804, 2, x_803);
x_805 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_799, x_804);
x_806 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_225, x_805);
if (lean::obj_tag(x_806) == 0)
{
obj* x_809; obj* x_810; obj* x_811; obj* x_812; 
lean::dec(x_4);
lean::dec(x_0);
x_809 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_806);
x_810 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_809);
x_811 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_810);
x_812 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_811);
return x_812;
}
else
{
obj* x_813; uint8 x_815; 
x_813 = lean::cnstr_get(x_806, 0);
lean::inc(x_813);
x_815 = lean::cnstr_get_scalar<uint8>(x_806, sizeof(void*)*1);
x_219 = x_806;
x_220 = x_813;
x_221 = x_815;
goto lbl_222;
}
}
else
{
obj* x_817; uint8 x_819; obj* x_820; obj* x_821; obj* x_822; obj* x_823; 
lean::dec(x_223);
x_817 = lean::cnstr_get(x_794, 0);
x_819 = lean::cnstr_get_scalar<uint8>(x_794, sizeof(void*)*1);
if (lean::is_exclusive(x_794)) {
 x_820 = x_794;
} else {
 lean::inc(x_817);
 lean::dec(x_794);
 x_820 = lean::box(0);
}
if (lean::is_scalar(x_820)) {
 x_821 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_821 = x_820;
}
lean::cnstr_set(x_821, 0, x_817);
lean::cnstr_set_scalar(x_821, sizeof(void*)*1, x_819);
x_822 = x_821;
x_823 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_225, x_822);
if (lean::obj_tag(x_823) == 0)
{
obj* x_826; obj* x_827; obj* x_828; obj* x_829; 
lean::dec(x_4);
lean::dec(x_0);
x_826 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_142, x_823);
x_827 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_826);
x_828 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_827);
x_829 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_828);
return x_829;
}
else
{
obj* x_830; uint8 x_832; 
x_830 = lean::cnstr_get(x_823, 0);
lean::inc(x_830);
x_832 = lean::cnstr_get_scalar<uint8>(x_823, sizeof(void*)*1);
x_219 = x_823;
x_220 = x_830;
x_221 = x_832;
goto lbl_222;
}
}
}
}
lbl_148:
{
obj* x_833; 
x_833 = l_lean_ir_parse__uint16(x_146);
if (lean::obj_tag(x_833) == 0)
{
obj* x_834; obj* x_836; obj* x_838; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; 
x_834 = lean::cnstr_get(x_833, 0);
x_836 = lean::cnstr_get(x_833, 1);
x_838 = lean::cnstr_get(x_833, 2);
if (lean::is_exclusive(x_833)) {
 x_840 = x_833;
} else {
 lean::inc(x_834);
 lean::inc(x_836);
 lean::inc(x_838);
 lean::dec(x_833);
 x_840 = lean::box(0);
}
x_841 = lean::apply_1(x_145, x_834);
x_842 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_840)) {
 x_843 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_843 = x_840;
}
lean::cnstr_set(x_843, 0, x_841);
lean::cnstr_set(x_843, 1, x_836);
lean::cnstr_set(x_843, 2, x_842);
x_844 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_838, x_843);
x_845 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_147, x_844);
if (lean::obj_tag(x_845) == 0)
{
obj* x_848; obj* x_849; obj* x_850; 
lean::dec(x_4);
lean::dec(x_0);
x_848 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_845);
x_849 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_848);
x_850 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_849);
return x_850;
}
else
{
obj* x_851; uint8 x_853; 
x_851 = lean::cnstr_get(x_845, 0);
lean::inc(x_851);
x_853 = lean::cnstr_get_scalar<uint8>(x_845, sizeof(void*)*1);
x_141 = x_845;
x_142 = x_851;
x_143 = x_853;
goto lbl_144;
}
}
else
{
obj* x_855; uint8 x_857; obj* x_858; obj* x_859; obj* x_860; obj* x_861; 
lean::dec(x_145);
x_855 = lean::cnstr_get(x_833, 0);
x_857 = lean::cnstr_get_scalar<uint8>(x_833, sizeof(void*)*1);
if (lean::is_exclusive(x_833)) {
 x_858 = x_833;
} else {
 lean::inc(x_855);
 lean::dec(x_833);
 x_858 = lean::box(0);
}
if (lean::is_scalar(x_858)) {
 x_859 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_859 = x_858;
}
lean::cnstr_set(x_859, 0, x_855);
lean::cnstr_set_scalar(x_859, sizeof(void*)*1, x_857);
x_860 = x_859;
x_861 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_147, x_860);
if (lean::obj_tag(x_861) == 0)
{
obj* x_864; obj* x_865; obj* x_866; 
lean::dec(x_4);
lean::dec(x_0);
x_864 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_83, x_861);
x_865 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_864);
x_866 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_865);
return x_866;
}
else
{
obj* x_867; uint8 x_869; 
x_867 = lean::cnstr_get(x_861, 0);
lean::inc(x_867);
x_869 = lean::cnstr_get_scalar<uint8>(x_861, sizeof(void*)*1);
x_141 = x_861;
x_142 = x_867;
x_143 = x_869;
goto lbl_144;
}
}
}
}
}
}
lbl_14:
{
obj* x_870; 
x_870 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(x_12);
if (lean::obj_tag(x_870) == 0)
{
obj* x_871; obj* x_873; obj* x_875; obj* x_877; obj* x_878; obj* x_879; obj* x_880; obj* x_881; obj* x_882; 
x_871 = lean::cnstr_get(x_870, 0);
x_873 = lean::cnstr_get(x_870, 1);
x_875 = lean::cnstr_get(x_870, 2);
if (lean::is_exclusive(x_870)) {
 x_877 = x_870;
} else {
 lean::inc(x_871);
 lean::inc(x_873);
 lean::inc(x_875);
 lean::dec(x_870);
 x_877 = lean::box(0);
}
x_878 = lean::apply_1(x_11, x_871);
x_879 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_877)) {
 x_880 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_880 = x_877;
}
lean::cnstr_set(x_880, 0, x_878);
lean::cnstr_set(x_880, 1, x_873);
lean::cnstr_set(x_880, 2, x_879);
x_881 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_875, x_880);
x_882 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_881);
x_9 = x_882;
goto lbl_10;
}
else
{
obj* x_884; uint8 x_886; obj* x_887; obj* x_888; obj* x_889; obj* x_890; 
lean::dec(x_11);
x_884 = lean::cnstr_get(x_870, 0);
x_886 = lean::cnstr_get_scalar<uint8>(x_870, sizeof(void*)*1);
if (lean::is_exclusive(x_870)) {
 x_887 = x_870;
} else {
 lean::inc(x_884);
 lean::dec(x_870);
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
x_890 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_889);
x_9 = x_890;
goto lbl_10;
}
}
}
else
{
obj* x_892; uint8 x_894; obj* x_895; obj* x_896; obj* x_897; 
lean::dec(x_0);
x_892 = lean::cnstr_get(x_3, 0);
x_894 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_895 = x_3;
} else {
 lean::inc(x_892);
 lean::dec(x_3);
 x_895 = lean::box(0);
}
if (lean::is_scalar(x_895)) {
 x_896 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_896 = x_895;
}
lean::cnstr_set(x_896, 0, x_892);
lean::cnstr_set_scalar(x_896, sizeof(void*)*1, x_894);
x_897 = x_896;
return x_897;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_14; obj* x_16; obj* x_19; 
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_lean_ir_parse__var(x_14);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
x_24 = lean::cnstr_get(x_19, 2);
if (lean::is_exclusive(x_19)) {
 x_26 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_19);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__4), 3, 1);
lean::closure_set(x_27, 0, x_20);
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_26)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_26;
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
obj* x_45; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_45 = lean::cnstr_get(x_19, 0);
x_47 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_48 = x_19;
} else {
 lean::inc(x_45);
 lean::dec(x_19);
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
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_54; obj* x_56; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 2);
lean::inc(x_56);
lean::dec(x_51);
x_7 = x_52;
x_8 = x_54;
x_9 = x_56;
goto lbl_10;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_51, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1);
if (lean::is_exclusive(x_51)) {
 x_62 = x_51;
} else {
 lean::inc(x_59);
 lean::dec(x_51);
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
x_1 = x_64;
goto lbl_2;
}
}
}
else
{
obj* x_65; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_13, 0);
x_67 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_68 = x_13;
} else {
 lean::inc(x_65);
 lean::dec(x_13);
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
x_1 = x_70;
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
obj* x_72; uint8 x_74; obj* x_75; obj* x_76; uint8 x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
x_72 = lean::cnstr_get(x_1, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_74 == 0)
{
obj* x_88; obj* x_90; 
lean::dec(x_1);
x_88 = l_lean_ir_parse__instr___closed__2;
lean::inc(x_0);
x_90 = l_lean_ir_keyword(x_88, x_0);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_93; obj* x_96; 
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 2);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_ir_parse__var(x_91);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_97 = lean::cnstr_get(x_96, 0);
x_99 = lean::cnstr_get(x_96, 1);
x_101 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 x_103 = x_96;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__3___boxed), 3, 1);
lean::closure_set(x_104, 0, x_97);
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_99);
lean::cnstr_set(x_106, 2, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_111; obj* x_113; 
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_108, 2);
lean::inc(x_113);
lean::dec(x_108);
x_83 = x_109;
x_84 = x_111;
x_85 = x_113;
goto lbl_86;
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_121; obj* x_122; 
x_116 = lean::cnstr_get(x_108, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_108, sizeof(void*)*1);
if (lean::is_exclusive(x_108)) {
 x_119 = x_108;
} else {
 lean::inc(x_116);
 lean::dec(x_108);
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
x_75 = x_122;
x_76 = x_116;
x_77 = x_118;
goto lbl_78;
}
}
else
{
obj* x_123; uint8 x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_123 = lean::cnstr_get(x_96, 0);
x_125 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_126 = x_96;
} else {
 lean::inc(x_123);
 lean::dec(x_96);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_123);
lean::cnstr_set_scalar(x_127, sizeof(void*)*1, x_125);
x_128 = x_127;
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_128);
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
x_83 = x_130;
x_84 = x_132;
x_85 = x_134;
goto lbl_86;
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_142; obj* x_143; 
x_137 = lean::cnstr_get(x_129, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_129, sizeof(void*)*1);
if (lean::is_exclusive(x_129)) {
 x_140 = x_129;
} else {
 lean::inc(x_137);
 lean::dec(x_129);
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
x_75 = x_143;
x_76 = x_137;
x_77 = x_139;
goto lbl_78;
}
}
}
else
{
obj* x_144; uint8 x_146; obj* x_147; obj* x_149; obj* x_150; 
x_144 = lean::cnstr_get(x_90, 0);
x_146 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (lean::is_exclusive(x_90)) {
 x_147 = x_90;
} else {
 lean::inc(x_144);
 lean::dec(x_90);
 x_147 = lean::box(0);
}
lean::inc(x_144);
if (lean::is_scalar(x_147)) {
 x_149 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_149 = x_147;
}
lean::cnstr_set(x_149, 0, x_144);
lean::cnstr_set_scalar(x_149, sizeof(void*)*1, x_146);
x_150 = x_149;
x_75 = x_150;
x_76 = x_144;
x_77 = x_146;
goto lbl_78;
}
}
else
{
lean::dec(x_0);
lean::dec(x_72);
return x_1;
}
lbl_78:
{
obj* x_153; obj* x_154; uint8 x_155; obj* x_157; obj* x_158; obj* x_159; obj* x_161; obj* x_162; obj* x_163; 
if (x_77 == 0)
{
obj* x_166; obj* x_168; 
lean::dec(x_75);
x_166 = l_lean_ir_parse__instr___closed__1;
lean::inc(x_0);
x_168 = l_lean_ir_keyword(x_166, x_0);
if (lean::obj_tag(x_168) == 0)
{
obj* x_169; obj* x_171; obj* x_174; 
x_169 = lean::cnstr_get(x_168, 1);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 2);
lean::inc(x_171);
lean::dec(x_168);
x_174 = l_lean_ir_parse__var(x_169);
if (lean::obj_tag(x_174) == 0)
{
obj* x_175; obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
x_175 = lean::cnstr_get(x_174, 0);
x_177 = lean::cnstr_get(x_174, 1);
x_179 = lean::cnstr_get(x_174, 2);
if (lean::is_exclusive(x_174)) {
 x_181 = x_174;
} else {
 lean::inc(x_175);
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_174);
 x_181 = lean::box(0);
}
x_182 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__2___boxed), 3, 1);
lean::closure_set(x_182, 0, x_175);
x_183 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_181)) {
 x_184 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_184 = x_181;
}
lean::cnstr_set(x_184, 0, x_182);
lean::cnstr_set(x_184, 1, x_177);
lean::cnstr_set(x_184, 2, x_183);
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_179, x_184);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_185);
if (lean::obj_tag(x_186) == 0)
{
obj* x_187; obj* x_189; obj* x_191; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_186, 2);
lean::inc(x_191);
lean::dec(x_186);
x_161 = x_187;
x_162 = x_189;
x_163 = x_191;
goto lbl_164;
}
else
{
obj* x_194; uint8 x_196; obj* x_197; obj* x_199; obj* x_200; 
x_194 = lean::cnstr_get(x_186, 0);
x_196 = lean::cnstr_get_scalar<uint8>(x_186, sizeof(void*)*1);
if (lean::is_exclusive(x_186)) {
 x_197 = x_186;
} else {
 lean::inc(x_194);
 lean::dec(x_186);
 x_197 = lean::box(0);
}
lean::inc(x_194);
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_194);
lean::cnstr_set_scalar(x_199, sizeof(void*)*1, x_196);
x_200 = x_199;
x_153 = x_200;
x_154 = x_194;
x_155 = x_196;
goto lbl_156;
}
}
else
{
obj* x_201; uint8 x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_201 = lean::cnstr_get(x_174, 0);
x_203 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
if (lean::is_exclusive(x_174)) {
 x_204 = x_174;
} else {
 lean::inc(x_201);
 lean::dec(x_174);
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
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_206);
if (lean::obj_tag(x_207) == 0)
{
obj* x_208; obj* x_210; obj* x_212; 
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_207, 2);
lean::inc(x_212);
lean::dec(x_207);
x_161 = x_208;
x_162 = x_210;
x_163 = x_212;
goto lbl_164;
}
else
{
obj* x_215; uint8 x_217; obj* x_218; obj* x_220; obj* x_221; 
x_215 = lean::cnstr_get(x_207, 0);
x_217 = lean::cnstr_get_scalar<uint8>(x_207, sizeof(void*)*1);
if (lean::is_exclusive(x_207)) {
 x_218 = x_207;
} else {
 lean::inc(x_215);
 lean::dec(x_207);
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
x_153 = x_221;
x_154 = x_215;
x_155 = x_217;
goto lbl_156;
}
}
}
else
{
obj* x_222; uint8 x_224; obj* x_225; obj* x_227; obj* x_228; 
x_222 = lean::cnstr_get(x_168, 0);
x_224 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_exclusive(x_168)) {
 x_225 = x_168;
} else {
 lean::inc(x_222);
 lean::dec(x_168);
 x_225 = lean::box(0);
}
lean::inc(x_222);
if (lean::is_scalar(x_225)) {
 x_227 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_227 = x_225;
}
lean::cnstr_set(x_227, 0, x_222);
lean::cnstr_set_scalar(x_227, sizeof(void*)*1, x_224);
x_228 = x_227;
x_153 = x_228;
x_154 = x_222;
x_155 = x_224;
goto lbl_156;
}
}
else
{
obj* x_231; 
lean::dec(x_76);
lean::dec(x_0);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_75);
return x_231;
}
lbl_156:
{
obj* x_232; obj* x_233; obj* x_234; 
if (x_155 == 0)
{
obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_153);
x_237 = l_lean_ir_parse__typed__assignment___closed__5;
x_238 = l_lean_ir_str2unop;
lean::inc(x_0);
x_240 = l_lean_ir_parse__key2val___main___rarg(x_237, x_238, x_0);
if (lean::obj_tag(x_240) == 0)
{
obj* x_241; obj* x_243; obj* x_245; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
x_241 = lean::cnstr_get(x_240, 0);
x_243 = lean::cnstr_get(x_240, 1);
x_245 = lean::cnstr_get(x_240, 2);
if (lean::is_exclusive(x_240)) {
 x_247 = x_240;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::inc(x_245);
 lean::dec(x_240);
 x_247 = lean::box(0);
}
x_248 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__1___boxed), 2, 1);
lean::closure_set(x_248, 0, x_241);
x_249 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_247)) {
 x_250 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_250 = x_247;
}
lean::cnstr_set(x_250, 0, x_248);
lean::cnstr_set(x_250, 1, x_243);
lean::cnstr_set(x_250, 2, x_249);
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_245, x_250);
if (lean::obj_tag(x_251) == 0)
{
obj* x_252; obj* x_254; obj* x_256; 
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_251, 2);
lean::inc(x_256);
lean::dec(x_251);
x_232 = x_252;
x_233 = x_254;
x_234 = x_256;
goto lbl_235;
}
else
{
obj* x_259; uint8 x_261; obj* x_262; 
x_259 = lean::cnstr_get(x_251, 0);
x_261 = lean::cnstr_get_scalar<uint8>(x_251, sizeof(void*)*1);
if (lean::is_exclusive(x_251)) {
 lean::cnstr_set(x_251, 0, lean::box(0));
 x_262 = x_251;
} else {
 lean::inc(x_259);
 lean::dec(x_251);
 x_262 = lean::box(0);
}
if (x_261 == 0)
{
obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
lean::dec(x_262);
x_264 = l_lean_ir_parse__assignment(x_0);
x_265 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_259, x_264);
x_266 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_265);
x_267 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_266);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_267);
return x_268;
}
else
{
obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_0);
if (lean::is_scalar(x_262)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_262;
}
lean::cnstr_set(x_270, 0, x_259);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_261);
x_271 = x_270;
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_271);
x_273 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_272);
x_274 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_273);
return x_274;
}
}
}
else
{
obj* x_275; uint8 x_277; obj* x_278; 
x_275 = lean::cnstr_get(x_240, 0);
x_277 = lean::cnstr_get_scalar<uint8>(x_240, sizeof(void*)*1);
if (lean::is_exclusive(x_240)) {
 lean::cnstr_set(x_240, 0, lean::box(0));
 x_278 = x_240;
} else {
 lean::inc(x_275);
 lean::dec(x_240);
 x_278 = lean::box(0);
}
if (x_277 == 0)
{
obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_278);
x_280 = l_lean_ir_parse__assignment(x_0);
x_281 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_275, x_280);
x_282 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_281);
x_283 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_282);
x_284 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_283);
return x_284;
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
lean::dec(x_0);
if (lean::is_scalar(x_278)) {
 x_286 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_286 = x_278;
}
lean::cnstr_set(x_286, 0, x_275);
lean::cnstr_set_scalar(x_286, sizeof(void*)*1, x_277);
x_287 = x_286;
x_288 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_287);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_288);
x_290 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_289);
return x_290;
}
}
}
else
{
obj* x_293; obj* x_294; 
lean::dec(x_154);
lean::dec(x_0);
x_293 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_153);
x_294 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_293);
return x_294;
}
lbl_235:
{
obj* x_295; 
x_295 = l_lean_ir_parse__var(x_233);
if (lean::obj_tag(x_295) == 0)
{
obj* x_296; obj* x_298; obj* x_300; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; 
x_296 = lean::cnstr_get(x_295, 0);
x_298 = lean::cnstr_get(x_295, 1);
x_300 = lean::cnstr_get(x_295, 2);
if (lean::is_exclusive(x_295)) {
 x_302 = x_295;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::inc(x_300);
 lean::dec(x_295);
 x_302 = lean::box(0);
}
x_303 = lean::apply_1(x_232, x_296);
x_304 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_302)) {
 x_305 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_305 = x_302;
}
lean::cnstr_set(x_305, 0, x_303);
lean::cnstr_set(x_305, 1, x_298);
lean::cnstr_set(x_305, 2, x_304);
x_306 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_300, x_305);
x_307 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_234, x_306);
if (lean::obj_tag(x_307) == 0)
{
obj* x_309; obj* x_310; obj* x_311; 
lean::dec(x_0);
x_309 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_307);
x_310 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_309);
x_311 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_310);
return x_311;
}
else
{
obj* x_312; uint8 x_314; 
x_312 = lean::cnstr_get(x_307, 0);
lean::inc(x_312);
x_314 = lean::cnstr_get_scalar<uint8>(x_307, sizeof(void*)*1);
if (x_314 == 0)
{
obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
lean::dec(x_307);
x_316 = l_lean_ir_parse__assignment(x_0);
x_317 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_312, x_316);
x_318 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_317);
x_319 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_318);
x_320 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_319);
return x_320;
}
else
{
obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_0);
lean::dec(x_312);
x_323 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_307);
x_324 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_323);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_324);
return x_325;
}
}
}
else
{
obj* x_327; uint8 x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
lean::dec(x_232);
x_327 = lean::cnstr_get(x_295, 0);
x_329 = lean::cnstr_get_scalar<uint8>(x_295, sizeof(void*)*1);
if (lean::is_exclusive(x_295)) {
 x_330 = x_295;
} else {
 lean::inc(x_327);
 lean::dec(x_295);
 x_330 = lean::box(0);
}
if (lean::is_scalar(x_330)) {
 x_331 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_331 = x_330;
}
lean::cnstr_set(x_331, 0, x_327);
lean::cnstr_set_scalar(x_331, sizeof(void*)*1, x_329);
x_332 = x_331;
x_333 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_234, x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_335; obj* x_336; obj* x_337; 
lean::dec(x_0);
x_335 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_333);
x_336 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_335);
x_337 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_336);
return x_337;
}
else
{
obj* x_338; uint8 x_340; 
x_338 = lean::cnstr_get(x_333, 0);
lean::inc(x_338);
x_340 = lean::cnstr_get_scalar<uint8>(x_333, sizeof(void*)*1);
if (x_340 == 0)
{
obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; 
lean::dec(x_333);
x_342 = l_lean_ir_parse__assignment(x_0);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_338, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_343);
x_345 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_344);
x_346 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_345);
return x_346;
}
else
{
obj* x_349; obj* x_350; obj* x_351; 
lean::dec(x_0);
lean::dec(x_338);
x_349 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_154, x_333);
x_350 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_349);
x_351 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_350);
return x_351;
}
}
}
}
}
lbl_160:
{
obj* x_352; 
x_352 = l_lean_ir_parse__var(x_158);
if (lean::obj_tag(x_352) == 0)
{
obj* x_353; obj* x_355; obj* x_357; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
x_353 = lean::cnstr_get(x_352, 0);
x_355 = lean::cnstr_get(x_352, 1);
x_357 = lean::cnstr_get(x_352, 2);
if (lean::is_exclusive(x_352)) {
 x_359 = x_352;
} else {
 lean::inc(x_353);
 lean::inc(x_355);
 lean::inc(x_357);
 lean::dec(x_352);
 x_359 = lean::box(0);
}
x_360 = lean::apply_1(x_157, x_353);
x_361 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_359)) {
 x_362 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_362 = x_359;
}
lean::cnstr_set(x_362, 0, x_360);
lean::cnstr_set(x_362, 1, x_355);
lean::cnstr_set(x_362, 2, x_361);
x_363 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_362);
x_364 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_363);
if (lean::obj_tag(x_364) == 0)
{
obj* x_366; obj* x_367; 
lean::dec(x_0);
x_366 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_364);
x_367 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_366);
return x_367;
}
else
{
obj* x_368; uint8 x_370; 
x_368 = lean::cnstr_get(x_364, 0);
lean::inc(x_368);
x_370 = lean::cnstr_get_scalar<uint8>(x_364, sizeof(void*)*1);
x_153 = x_364;
x_154 = x_368;
x_155 = x_370;
goto lbl_156;
}
}
else
{
obj* x_372; uint8 x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; 
lean::dec(x_157);
x_372 = lean::cnstr_get(x_352, 0);
x_374 = lean::cnstr_get_scalar<uint8>(x_352, sizeof(void*)*1);
if (lean::is_exclusive(x_352)) {
 x_375 = x_352;
} else {
 lean::inc(x_372);
 lean::dec(x_352);
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
x_378 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_377);
if (lean::obj_tag(x_378) == 0)
{
obj* x_380; obj* x_381; 
lean::dec(x_0);
x_380 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_76, x_378);
x_381 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_380);
return x_381;
}
else
{
obj* x_382; uint8 x_384; 
x_382 = lean::cnstr_get(x_378, 0);
lean::inc(x_382);
x_384 = lean::cnstr_get_scalar<uint8>(x_378, sizeof(void*)*1);
x_153 = x_378;
x_154 = x_382;
x_155 = x_384;
goto lbl_156;
}
}
}
lbl_164:
{
obj* x_385; 
x_385 = l_lean_ir_parse__usize(x_162);
if (lean::obj_tag(x_385) == 0)
{
obj* x_386; obj* x_388; obj* x_390; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; 
x_386 = lean::cnstr_get(x_385, 0);
x_388 = lean::cnstr_get(x_385, 1);
x_390 = lean::cnstr_get(x_385, 2);
if (lean::is_exclusive(x_385)) {
 x_392 = x_385;
} else {
 lean::inc(x_386);
 lean::inc(x_388);
 lean::inc(x_390);
 lean::dec(x_385);
 x_392 = lean::box(0);
}
x_393 = lean::apply_1(x_161, x_386);
x_394 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_392)) {
 x_395 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_395 = x_392;
}
lean::cnstr_set(x_395, 0, x_393);
lean::cnstr_set(x_395, 1, x_388);
lean::cnstr_set(x_395, 2, x_394);
x_396 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_390, x_395);
x_397 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_396);
if (lean::obj_tag(x_397) == 0)
{
obj* x_398; obj* x_400; obj* x_402; 
x_398 = lean::cnstr_get(x_397, 0);
lean::inc(x_398);
x_400 = lean::cnstr_get(x_397, 1);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_397, 2);
lean::inc(x_402);
lean::dec(x_397);
x_157 = x_398;
x_158 = x_400;
x_159 = x_402;
goto lbl_160;
}
else
{
obj* x_405; uint8 x_407; obj* x_408; obj* x_410; obj* x_411; 
x_405 = lean::cnstr_get(x_397, 0);
x_407 = lean::cnstr_get_scalar<uint8>(x_397, sizeof(void*)*1);
if (lean::is_exclusive(x_397)) {
 x_408 = x_397;
} else {
 lean::inc(x_405);
 lean::dec(x_397);
 x_408 = lean::box(0);
}
lean::inc(x_405);
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*1, x_407);
x_411 = x_410;
x_153 = x_411;
x_154 = x_405;
x_155 = x_407;
goto lbl_156;
}
}
else
{
obj* x_413; uint8 x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; 
lean::dec(x_161);
x_413 = lean::cnstr_get(x_385, 0);
x_415 = lean::cnstr_get_scalar<uint8>(x_385, sizeof(void*)*1);
if (lean::is_exclusive(x_385)) {
 x_416 = x_385;
} else {
 lean::inc(x_413);
 lean::dec(x_385);
 x_416 = lean::box(0);
}
if (lean::is_scalar(x_416)) {
 x_417 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_417 = x_416;
}
lean::cnstr_set(x_417, 0, x_413);
lean::cnstr_set_scalar(x_417, sizeof(void*)*1, x_415);
x_418 = x_417;
x_419 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_418);
if (lean::obj_tag(x_419) == 0)
{
obj* x_420; obj* x_422; obj* x_424; 
x_420 = lean::cnstr_get(x_419, 0);
lean::inc(x_420);
x_422 = lean::cnstr_get(x_419, 1);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_419, 2);
lean::inc(x_424);
lean::dec(x_419);
x_157 = x_420;
x_158 = x_422;
x_159 = x_424;
goto lbl_160;
}
else
{
obj* x_427; uint8 x_429; obj* x_430; obj* x_432; obj* x_433; 
x_427 = lean::cnstr_get(x_419, 0);
x_429 = lean::cnstr_get_scalar<uint8>(x_419, sizeof(void*)*1);
if (lean::is_exclusive(x_419)) {
 x_430 = x_419;
} else {
 lean::inc(x_427);
 lean::dec(x_419);
 x_430 = lean::box(0);
}
lean::inc(x_427);
if (lean::is_scalar(x_430)) {
 x_432 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_432 = x_430;
}
lean::cnstr_set(x_432, 0, x_427);
lean::cnstr_set_scalar(x_432, sizeof(void*)*1, x_429);
x_433 = x_432;
x_153 = x_433;
x_154 = x_427;
x_155 = x_429;
goto lbl_156;
}
}
}
}
lbl_82:
{
obj* x_434; 
x_434 = l_lean_ir_parse__var(x_80);
if (lean::obj_tag(x_434) == 0)
{
obj* x_435; obj* x_437; obj* x_439; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; 
x_435 = lean::cnstr_get(x_434, 0);
x_437 = lean::cnstr_get(x_434, 1);
x_439 = lean::cnstr_get(x_434, 2);
if (lean::is_exclusive(x_434)) {
 x_441 = x_434;
} else {
 lean::inc(x_435);
 lean::inc(x_437);
 lean::inc(x_439);
 lean::dec(x_434);
 x_441 = lean::box(0);
}
x_442 = lean::apply_1(x_79, x_435);
x_443 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_441)) {
 x_444 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_444 = x_441;
}
lean::cnstr_set(x_444, 0, x_442);
lean::cnstr_set(x_444, 1, x_437);
lean::cnstr_set(x_444, 2, x_443);
x_445 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_439, x_444);
x_446 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_445);
if (lean::obj_tag(x_446) == 0)
{
obj* x_448; 
lean::dec(x_0);
x_448 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_446);
return x_448;
}
else
{
obj* x_449; uint8 x_451; 
x_449 = lean::cnstr_get(x_446, 0);
lean::inc(x_449);
x_451 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*1);
x_75 = x_446;
x_76 = x_449;
x_77 = x_451;
goto lbl_78;
}
}
else
{
obj* x_453; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; 
lean::dec(x_79);
x_453 = lean::cnstr_get(x_434, 0);
x_455 = lean::cnstr_get_scalar<uint8>(x_434, sizeof(void*)*1);
if (lean::is_exclusive(x_434)) {
 x_456 = x_434;
} else {
 lean::inc(x_453);
 lean::dec(x_434);
 x_456 = lean::box(0);
}
if (lean::is_scalar(x_456)) {
 x_457 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_457 = x_456;
}
lean::cnstr_set(x_457, 0, x_453);
lean::cnstr_set_scalar(x_457, sizeof(void*)*1, x_455);
x_458 = x_457;
x_459 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_458);
if (lean::obj_tag(x_459) == 0)
{
obj* x_461; 
lean::dec(x_0);
x_461 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_72, x_459);
return x_461;
}
else
{
obj* x_462; uint8 x_464; 
x_462 = lean::cnstr_get(x_459, 0);
lean::inc(x_462);
x_464 = lean::cnstr_get_scalar<uint8>(x_459, sizeof(void*)*1);
x_75 = x_459;
x_76 = x_462;
x_77 = x_464;
goto lbl_78;
}
}
}
lbl_86:
{
obj* x_465; 
x_465 = l_lean_ir_parse__uint16(x_84);
if (lean::obj_tag(x_465) == 0)
{
obj* x_466; obj* x_468; obj* x_470; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_465, 0);
x_468 = lean::cnstr_get(x_465, 1);
x_470 = lean::cnstr_get(x_465, 2);
if (lean::is_exclusive(x_465)) {
 x_472 = x_465;
} else {
 lean::inc(x_466);
 lean::inc(x_468);
 lean::inc(x_470);
 lean::dec(x_465);
 x_472 = lean::box(0);
}
x_473 = lean::apply_1(x_83, x_466);
x_474 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_472)) {
 x_475 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_475 = x_472;
}
lean::cnstr_set(x_475, 0, x_473);
lean::cnstr_set(x_475, 1, x_468);
lean::cnstr_set(x_475, 2, x_474);
x_476 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_470, x_475);
x_477 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_476);
if (lean::obj_tag(x_477) == 0)
{
obj* x_478; obj* x_480; obj* x_482; 
x_478 = lean::cnstr_get(x_477, 0);
lean::inc(x_478);
x_480 = lean::cnstr_get(x_477, 1);
lean::inc(x_480);
x_482 = lean::cnstr_get(x_477, 2);
lean::inc(x_482);
lean::dec(x_477);
x_79 = x_478;
x_80 = x_480;
x_81 = x_482;
goto lbl_82;
}
else
{
obj* x_485; uint8 x_487; obj* x_488; obj* x_490; obj* x_491; 
x_485 = lean::cnstr_get(x_477, 0);
x_487 = lean::cnstr_get_scalar<uint8>(x_477, sizeof(void*)*1);
if (lean::is_exclusive(x_477)) {
 x_488 = x_477;
} else {
 lean::inc(x_485);
 lean::dec(x_477);
 x_488 = lean::box(0);
}
lean::inc(x_485);
if (lean::is_scalar(x_488)) {
 x_490 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_490 = x_488;
}
lean::cnstr_set(x_490, 0, x_485);
lean::cnstr_set_scalar(x_490, sizeof(void*)*1, x_487);
x_491 = x_490;
x_75 = x_491;
x_76 = x_485;
x_77 = x_487;
goto lbl_78;
}
}
else
{
obj* x_493; uint8 x_495; obj* x_496; obj* x_497; obj* x_498; obj* x_499; 
lean::dec(x_83);
x_493 = lean::cnstr_get(x_465, 0);
x_495 = lean::cnstr_get_scalar<uint8>(x_465, sizeof(void*)*1);
if (lean::is_exclusive(x_465)) {
 x_496 = x_465;
} else {
 lean::inc(x_493);
 lean::dec(x_465);
 x_496 = lean::box(0);
}
if (lean::is_scalar(x_496)) {
 x_497 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_497 = x_496;
}
lean::cnstr_set(x_497, 0, x_493);
lean::cnstr_set_scalar(x_497, sizeof(void*)*1, x_495);
x_498 = x_497;
x_499 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_498);
if (lean::obj_tag(x_499) == 0)
{
obj* x_500; obj* x_502; obj* x_504; 
x_500 = lean::cnstr_get(x_499, 0);
lean::inc(x_500);
x_502 = lean::cnstr_get(x_499, 1);
lean::inc(x_502);
x_504 = lean::cnstr_get(x_499, 2);
lean::inc(x_504);
lean::dec(x_499);
x_79 = x_500;
x_80 = x_502;
x_81 = x_504;
goto lbl_82;
}
else
{
obj* x_507; uint8 x_509; obj* x_510; obj* x_512; obj* x_513; 
x_507 = lean::cnstr_get(x_499, 0);
x_509 = lean::cnstr_get_scalar<uint8>(x_499, sizeof(void*)*1);
if (lean::is_exclusive(x_499)) {
 x_510 = x_499;
} else {
 lean::inc(x_507);
 lean::dec(x_499);
 x_510 = lean::box(0);
}
lean::inc(x_507);
if (lean::is_scalar(x_510)) {
 x_512 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_512 = x_510;
}
lean::cnstr_set(x_512, 0, x_507);
lean::cnstr_set_scalar(x_512, sizeof(void*)*1, x_509);
x_513 = x_512;
x_75 = x_513;
x_76 = x_507;
x_77 = x_509;
goto lbl_78;
}
}
}
}
}
lbl_6:
{
obj* x_514; 
x_514 = l_lean_ir_parse__var(x_4);
if (lean::obj_tag(x_514) == 0)
{
obj* x_515; obj* x_517; obj* x_519; obj* x_521; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; 
x_515 = lean::cnstr_get(x_514, 0);
x_517 = lean::cnstr_get(x_514, 1);
x_519 = lean::cnstr_get(x_514, 2);
if (lean::is_exclusive(x_514)) {
 x_521 = x_514;
} else {
 lean::inc(x_515);
 lean::inc(x_517);
 lean::inc(x_519);
 lean::dec(x_514);
 x_521 = lean::box(0);
}
x_522 = lean::apply_1(x_3, x_515);
x_523 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_521)) {
 x_524 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_524 = x_521;
}
lean::cnstr_set(x_524, 0, x_522);
lean::cnstr_set(x_524, 1, x_517);
lean::cnstr_set(x_524, 2, x_523);
x_525 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_519, x_524);
x_526 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_525);
x_1 = x_526;
goto lbl_2;
}
else
{
obj* x_528; uint8 x_530; obj* x_531; obj* x_532; obj* x_533; obj* x_534; 
lean::dec(x_3);
x_528 = lean::cnstr_get(x_514, 0);
x_530 = lean::cnstr_get_scalar<uint8>(x_514, sizeof(void*)*1);
if (lean::is_exclusive(x_514)) {
 x_531 = x_514;
} else {
 lean::inc(x_528);
 lean::dec(x_514);
 x_531 = lean::box(0);
}
if (lean::is_scalar(x_531)) {
 x_532 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_532 = x_531;
}
lean::cnstr_set(x_532, 0, x_528);
lean::cnstr_set_scalar(x_532, sizeof(void*)*1, x_530);
x_533 = x_532;
x_534 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_533);
x_1 = x_534;
goto lbl_2;
}
}
lbl_10:
{
obj* x_535; 
x_535 = l_lean_ir_parse__var(x_8);
if (lean::obj_tag(x_535) == 0)
{
obj* x_536; obj* x_538; obj* x_540; obj* x_542; obj* x_543; obj* x_544; obj* x_545; obj* x_546; obj* x_547; 
x_536 = lean::cnstr_get(x_535, 0);
x_538 = lean::cnstr_get(x_535, 1);
x_540 = lean::cnstr_get(x_535, 2);
if (lean::is_exclusive(x_535)) {
 x_542 = x_535;
} else {
 lean::inc(x_536);
 lean::inc(x_538);
 lean::inc(x_540);
 lean::dec(x_535);
 x_542 = lean::box(0);
}
x_543 = lean::apply_1(x_7, x_536);
x_544 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_542)) {
 x_545 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_545 = x_542;
}
lean::cnstr_set(x_545, 0, x_543);
lean::cnstr_set(x_545, 1, x_538);
lean::cnstr_set(x_545, 2, x_544);
x_546 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_540, x_545);
x_547 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_546);
if (lean::obj_tag(x_547) == 0)
{
obj* x_548; obj* x_550; obj* x_552; 
x_548 = lean::cnstr_get(x_547, 0);
lean::inc(x_548);
x_550 = lean::cnstr_get(x_547, 1);
lean::inc(x_550);
x_552 = lean::cnstr_get(x_547, 2);
lean::inc(x_552);
lean::dec(x_547);
x_3 = x_548;
x_4 = x_550;
x_5 = x_552;
goto lbl_6;
}
else
{
obj* x_555; uint8 x_557; obj* x_558; obj* x_559; obj* x_560; 
x_555 = lean::cnstr_get(x_547, 0);
x_557 = lean::cnstr_get_scalar<uint8>(x_547, sizeof(void*)*1);
if (lean::is_exclusive(x_547)) {
 x_558 = x_547;
} else {
 lean::inc(x_555);
 lean::dec(x_547);
 x_558 = lean::box(0);
}
if (lean::is_scalar(x_558)) {
 x_559 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_559 = x_558;
}
lean::cnstr_set(x_559, 0, x_555);
lean::cnstr_set_scalar(x_559, sizeof(void*)*1, x_557);
x_560 = x_559;
x_1 = x_560;
goto lbl_2;
}
}
else
{
obj* x_562; uint8 x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; 
lean::dec(x_7);
x_562 = lean::cnstr_get(x_535, 0);
x_564 = lean::cnstr_get_scalar<uint8>(x_535, sizeof(void*)*1);
if (lean::is_exclusive(x_535)) {
 x_565 = x_535;
} else {
 lean::inc(x_562);
 lean::dec(x_535);
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
x_568 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_567);
if (lean::obj_tag(x_568) == 0)
{
obj* x_569; obj* x_571; obj* x_573; 
x_569 = lean::cnstr_get(x_568, 0);
lean::inc(x_569);
x_571 = lean::cnstr_get(x_568, 1);
lean::inc(x_571);
x_573 = lean::cnstr_get(x_568, 2);
lean::inc(x_573);
lean::dec(x_568);
x_3 = x_569;
x_4 = x_571;
x_5 = x_573;
goto lbl_6;
}
else
{
obj* x_576; uint8 x_578; obj* x_579; obj* x_580; obj* x_581; 
x_576 = lean::cnstr_get(x_568, 0);
x_578 = lean::cnstr_get_scalar<uint8>(x_568, sizeof(void*)*1);
if (lean::is_exclusive(x_568)) {
 x_579 = x_568;
} else {
 lean::inc(x_576);
 lean::dec(x_568);
 x_579 = lean::box(0);
}
if (lean::is_scalar(x_579)) {
 x_580 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_580 = x_579;
}
lean::cnstr_set(x_580, 0, x_576);
lean::cnstr_set_scalar(x_580, sizeof(void*)*1, x_578);
x_581 = x_580;
x_1 = x_581;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
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
obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_39 = lean::cnstr_get(x_38, 1);
x_41 = lean::cnstr_get(x_38, 2);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_43 = x_38;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_38);
 x_43 = lean::box(0);
}
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_6);
lean::cnstr_set(x_44, 1, x_23);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_43;
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
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_6);
lean::dec(x_23);
x_68 = lean::cnstr_get(x_38, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 x_71 = x_38;
} else {
 lean::inc(x_68);
 lean::dec(x_38);
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
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_73);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_74);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_76);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_81; obj* x_83; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_1 = x_79;
x_2 = x_81;
x_3 = x_83;
goto lbl_4;
}
else
{
obj* x_86; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; 
x_86 = lean::cnstr_get(x_78, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (lean::is_exclusive(x_78)) {
 x_89 = x_78;
} else {
 lean::inc(x_86);
 lean::dec(x_78);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_86);
lean::cnstr_set_scalar(x_90, sizeof(void*)*1, x_88);
x_91 = x_90;
return x_91;
}
}
}
else
{
obj* x_94; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_6);
lean::dec(x_23);
x_94 = lean::cnstr_get(x_31, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (lean::is_exclusive(x_31)) {
 x_97 = x_31;
} else {
 lean::inc(x_94);
 lean::dec(x_31);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_100);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_101);
x_103 = l_lean_parser_parsec__t_try__mk__res___rarg(x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_106; obj* x_108; 
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_103, 2);
lean::inc(x_108);
lean::dec(x_103);
x_1 = x_104;
x_2 = x_106;
x_3 = x_108;
goto lbl_4;
}
else
{
obj* x_111; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; 
x_111 = lean::cnstr_get(x_103, 0);
x_113 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*1);
if (lean::is_exclusive(x_103)) {
 x_114 = x_103;
} else {
 lean::inc(x_111);
 lean::dec(x_103);
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
return x_116;
}
}
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_6);
x_118 = lean::cnstr_get(x_22, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_exclusive(x_22)) {
 x_121 = x_22;
} else {
 lean::inc(x_118);
 lean::dec(x_22);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = x_122;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_123);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_124);
x_126 = l_lean_parser_parsec__t_try__mk__res___rarg(x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_127; obj* x_129; obj* x_131; 
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_126, 2);
lean::inc(x_131);
lean::dec(x_126);
x_1 = x_127;
x_2 = x_129;
x_3 = x_131;
goto lbl_4;
}
else
{
obj* x_134; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; 
x_134 = lean::cnstr_get(x_126, 0);
x_136 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
if (lean::is_exclusive(x_126)) {
 x_137 = x_126;
} else {
 lean::inc(x_134);
 lean::dec(x_126);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_134);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_136);
x_139 = x_138;
return x_139;
}
}
}
else
{
obj* x_141; uint8 x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
lean::dec(x_6);
x_141 = lean::cnstr_get(x_14, 0);
x_143 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_144 = x_14;
} else {
 lean::inc(x_141);
 lean::dec(x_14);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_141);
lean::cnstr_set_scalar(x_145, sizeof(void*)*1, x_143);
x_146 = x_145;
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_146);
x_148 = l_lean_parser_parsec__t_try__mk__res___rarg(x_147);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_151; obj* x_153; 
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_148, 1);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_148, 2);
lean::inc(x_153);
lean::dec(x_148);
x_1 = x_149;
x_2 = x_151;
x_3 = x_153;
goto lbl_4;
}
else
{
obj* x_156; uint8 x_158; obj* x_159; obj* x_160; obj* x_161; 
x_156 = lean::cnstr_get(x_148, 0);
x_158 = lean::cnstr_get_scalar<uint8>(x_148, sizeof(void*)*1);
if (lean::is_exclusive(x_148)) {
 x_159 = x_148;
} else {
 lean::inc(x_156);
 lean::dec(x_148);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_156);
lean::cnstr_set_scalar(x_160, sizeof(void*)*1, x_158);
x_161 = x_160;
return x_161;
}
}
}
else
{
obj* x_162; obj* x_164; uint8 x_165; obj* x_166; obj* x_167; 
x_162 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_164 = x_5;
} else {
 lean::inc(x_162);
 lean::dec(x_5);
 x_164 = lean::box(0);
}
x_165 = 0;
if (lean::is_scalar(x_164)) {
 x_166 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_166 = x_164;
}
lean::cnstr_set(x_166, 0, x_162);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_165);
x_167 = x_166;
return x_167;
}
lbl_4:
{
obj* x_168; obj* x_170; obj* x_173; 
x_168 = lean::cnstr_get(x_1, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_1, 1);
lean::inc(x_170);
lean::dec(x_1);
x_173 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(x_2);
if (lean::obj_tag(x_173) == 0)
{
obj* x_174; obj* x_176; obj* x_178; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_174 = lean::cnstr_get(x_173, 0);
x_176 = lean::cnstr_get(x_173, 1);
x_178 = lean::cnstr_get(x_173, 2);
if (lean::is_exclusive(x_173)) {
 x_180 = x_173;
} else {
 lean::inc(x_174);
 lean::inc(x_176);
 lean::inc(x_178);
 lean::dec(x_173);
 x_180 = lean::box(0);
}
x_181 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_181, 0, x_168);
lean::cnstr_set(x_181, 1, x_174);
x_182 = lean::unbox(x_170);
lean::cnstr_set_scalar(x_181, sizeof(void*)*2, x_182);
x_183 = x_181;
x_184 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_180)) {
 x_185 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_185 = x_180;
}
lean::cnstr_set(x_185, 0, x_183);
lean::cnstr_set(x_185, 1, x_176);
lean::cnstr_set(x_185, 2, x_184);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_186);
return x_187;
}
else
{
obj* x_190; uint8 x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_170);
lean::dec(x_168);
x_190 = lean::cnstr_get(x_173, 0);
x_192 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
if (lean::is_exclusive(x_173)) {
 x_193 = x_173;
} else {
 lean::inc(x_190);
 lean::dec(x_173);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
x_10 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
x_11 = l_lean_ir_symbol(x_10, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_lean_ir_parse__blockid(x_12);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_23; 
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 2);
lean::inc(x_23);
lean::dec(x_18);
x_6 = x_19;
x_7 = x_21;
x_8 = x_23;
goto lbl_9;
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_5);
x_27 = lean::cnstr_get(x_18, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_30 = x_18;
} else {
 lean::inc(x_27);
 lean::dec(x_18);
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
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_5);
x_34 = lean::cnstr_get(x_11, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_37 = x_11;
} else {
 lean::inc(x_34);
 lean::dec(x_11);
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
return x_39;
}
lbl_9:
{
obj* x_41; obj* x_43; 
lean::inc(x_7);
x_41 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_5, x_7);
lean::dec(x_5);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; 
lean::dec(x_7);
x_46 = lean::box(0);
x_43 = x_46;
goto lbl_44;
}
else
{
obj* x_47; uint8 x_49; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (x_49 == 0)
{
obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_41);
x_51 = lean::box(0);
x_52 = lean::cnstr_get(x_47, 2);
lean::inc(x_52);
lean::dec(x_47);
x_55 = l_mjoin___rarg___closed__1;
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_56, 0, x_52);
lean::closure_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_6);
lean::cnstr_set(x_57, 1, x_51);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_58, 0, x_56);
lean::closure_set(x_58, 1, x_55);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_7);
lean::cnstr_set(x_60, 2, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_60);
return x_61;
}
else
{
obj* x_64; 
lean::dec(x_7);
lean::dec(x_47);
x_64 = lean::box(0);
x_43 = x_64;
goto lbl_44;
}
}
lbl_44:
{
lean::dec(x_43);
if (lean::obj_tag(x_41) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_66 = lean::cnstr_get(x_41, 0);
x_68 = lean::cnstr_get(x_41, 1);
x_70 = lean::cnstr_get(x_41, 2);
if (lean::is_exclusive(x_41)) {
 x_72 = x_41;
} else {
 lean::inc(x_66);
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_41);
 x_72 = lean::box(0);
}
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_6);
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
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_76);
return x_77;
}
else
{
obj* x_79; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_6);
x_79 = lean::cnstr_get(x_41, 0);
x_81 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_82 = x_41;
} else {
 lean::inc(x_79);
 lean::dec(x_41);
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
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_84);
return x_85;
}
}
}
}
else
{
obj* x_86; obj* x_87; 
x_86 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
x_87 = l_lean_ir_symbol(x_86, x_1);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_88 = lean::cnstr_get(x_87, 1);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 2);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_ir_parse__blockid(x_88);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_95 = lean::cnstr_get(x_94, 0);
x_97 = lean::cnstr_get(x_94, 1);
x_99 = lean::cnstr_get(x_94, 2);
if (lean::is_exclusive(x_94)) {
 x_101 = x_94;
} else {
 lean::inc(x_95);
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_94);
 x_101 = lean::box(0);
}
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_95);
lean::cnstr_set(x_103, 1, x_102);
x_104 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_101)) {
 x_105 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_105 = x_101;
}
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_97);
lean::cnstr_set(x_105, 2, x_104);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_99, x_105);
return x_106;
}
else
{
obj* x_107; uint8 x_109; obj* x_110; obj* x_111; obj* x_112; 
x_107 = lean::cnstr_get(x_94, 0);
x_109 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
if (lean::is_exclusive(x_94)) {
 x_110 = x_94;
} else {
 lean::inc(x_107);
 lean::dec(x_94);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set_scalar(x_111, sizeof(void*)*1, x_109);
x_112 = x_111;
return x_112;
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; 
x_113 = lean::cnstr_get(x_87, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
if (lean::is_exclusive(x_87)) {
 x_116 = x_87;
} else {
 lean::inc(x_113);
 lean::dec(x_87);
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
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__terminator___spec__3(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_13; obj* x_15; obj* x_17; obj* x_20; 
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 2);
lean::inc(x_17);
lean::dec(x_12);
x_20 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__terminator___spec__2(x_15);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
x_25 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_20);
 x_27 = lean::box(0);
}
x_28 = lean::apply_1(x_13, x_21);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_27;
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
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_13);
x_33 = lean::cnstr_get(x_20, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_36 = x_20;
} else {
 lean::inc(x_33);
 lean::dec(x_20);
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
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_38);
return x_39;
}
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_12, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_43 = x_12;
} else {
 lean::inc(x_40);
 lean::dec(x_12);
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
return x_45;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_1, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_49 = x_1;
} else {
 lean::inc(x_46);
 lean::dec(x_1);
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
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_ir_parse__blockid(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_11, 0);
x_14 = lean::cnstr_get(x_11, 1);
x_16 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
x_19 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_19, 0, x_12);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
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
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_11, 0);
x_26 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_27 = x_11;
} else {
 lean::inc(x_24);
 lean::dec(x_11);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_26);
x_29 = x_28;
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_29);
x_1 = x_30;
goto lbl_2;
}
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_5, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_34 = x_5;
} else {
 lean::inc(x_31);
 lean::dec(x_5);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_1 = x_36;
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
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_40 == 0)
{
obj* x_46; obj* x_48; 
lean::dec(x_1);
x_46 = l_lean_ir_parse__terminator___closed__2;
lean::inc(x_0);
x_48 = l_lean_ir_keyword(x_46, x_0);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_54; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 2);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_ir_parse__var(x_49);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_55 = lean::cnstr_get(x_54, 0);
x_57 = lean::cnstr_get(x_54, 1);
x_59 = lean::cnstr_get(x_54, 2);
if (lean::is_exclusive(x_54)) {
 x_61 = x_54;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_54);
 x_61 = lean::box(0);
}
x_62 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_62, 0, x_55);
x_63 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_57);
lean::cnstr_set(x_64, 2, x_63);
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_64);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; 
lean::dec(x_0);
x_68 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_66);
return x_68;
}
else
{
obj* x_69; uint8 x_71; 
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
x_41 = x_66;
x_42 = x_69;
x_43 = x_71;
goto lbl_44;
}
}
else
{
obj* x_72; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_72 = lean::cnstr_get(x_54, 0);
x_74 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_75 = x_54;
} else {
 lean::inc(x_72);
 lean::dec(x_54);
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
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; 
lean::dec(x_0);
x_80 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_78);
return x_80;
}
else
{
obj* x_81; uint8 x_83; 
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
x_41 = x_78;
x_42 = x_81;
x_43 = x_83;
goto lbl_44;
}
}
}
else
{
obj* x_84; uint8 x_86; obj* x_87; obj* x_89; obj* x_90; 
x_84 = lean::cnstr_get(x_48, 0);
x_86 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_exclusive(x_48)) {
 x_87 = x_48;
} else {
 lean::inc(x_84);
 lean::dec(x_48);
 x_87 = lean::box(0);
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
x_41 = x_90;
x_42 = x_84;
x_43 = x_86;
goto lbl_44;
}
}
else
{
lean::dec(x_0);
lean::dec(x_38);
return x_1;
}
lbl_44:
{
obj* x_93; obj* x_94; obj* x_95; 
if (x_43 == 0)
{
obj* x_98; obj* x_99; 
lean::dec(x_41);
x_98 = l_lean_ir_parse__terminator___closed__1;
x_99 = l_lean_ir_keyword(x_98, x_0);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; obj* x_102; obj* x_105; 
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_99, 2);
lean::inc(x_102);
lean::dec(x_99);
x_105 = l_lean_ir_parse__var(x_100);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_106 = lean::cnstr_get(x_105, 0);
x_108 = lean::cnstr_get(x_105, 1);
x_110 = lean::cnstr_get(x_105, 2);
if (lean::is_exclusive(x_105)) {
 x_112 = x_105;
} else {
 lean::inc(x_106);
 lean::inc(x_108);
 lean::inc(x_110);
 lean::dec(x_105);
 x_112 = lean::box(0);
}
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__terminator___lambda__1), 2, 1);
lean::closure_set(x_113, 0, x_106);
x_114 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_112)) {
 x_115 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_115 = x_112;
}
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_108);
lean::cnstr_set(x_115, 2, x_114);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_115);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_116);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_120; obj* x_122; 
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 2);
lean::inc(x_122);
lean::dec(x_117);
x_93 = x_118;
x_94 = x_120;
x_95 = x_122;
goto lbl_96;
}
else
{
obj* x_125; uint8 x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_125 = lean::cnstr_get(x_117, 0);
x_127 = lean::cnstr_get_scalar<uint8>(x_117, sizeof(void*)*1);
if (lean::is_exclusive(x_117)) {
 x_128 = x_117;
} else {
 lean::inc(x_125);
 lean::dec(x_117);
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
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_130);
x_132 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_131);
return x_132;
}
}
else
{
obj* x_133; uint8 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_133 = lean::cnstr_get(x_105, 0);
x_135 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (lean::is_exclusive(x_105)) {
 x_136 = x_105;
} else {
 lean::inc(x_133);
 lean::dec(x_105);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_133);
lean::cnstr_set_scalar(x_137, sizeof(void*)*1, x_135);
x_138 = x_137;
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_142; obj* x_144; 
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_139, 2);
lean::inc(x_144);
lean::dec(x_139);
x_93 = x_140;
x_94 = x_142;
x_95 = x_144;
goto lbl_96;
}
else
{
obj* x_147; uint8 x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_147 = lean::cnstr_get(x_139, 0);
x_149 = lean::cnstr_get_scalar<uint8>(x_139, sizeof(void*)*1);
if (lean::is_exclusive(x_139)) {
 x_150 = x_139;
} else {
 lean::inc(x_147);
 lean::dec(x_139);
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
x_153 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_152);
x_154 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_153);
return x_154;
}
}
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_155 = lean::cnstr_get(x_99, 0);
x_157 = lean::cnstr_get_scalar<uint8>(x_99, sizeof(void*)*1);
if (lean::is_exclusive(x_99)) {
 x_158 = x_99;
} else {
 lean::inc(x_155);
 lean::dec(x_99);
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
x_161 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_160);
x_162 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_161);
return x_162;
}
}
else
{
obj* x_165; 
lean::dec(x_0);
lean::dec(x_42);
x_165 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_41);
return x_165;
}
lbl_96:
{
obj* x_166; obj* x_167; obj* x_168; obj* x_170; obj* x_171; 
x_170 = l_list_repr___main___rarg___closed__2;
x_171 = l_lean_ir_symbol(x_170, x_94);
if (lean::obj_tag(x_171) == 0)
{
obj* x_172; obj* x_174; obj* x_177; obj* x_178; 
x_172 = lean::cnstr_get(x_171, 1);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_171, 2);
lean::inc(x_174);
lean::dec(x_171);
x_177 = l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(x_172);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_177);
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
x_166 = x_179;
x_167 = x_181;
x_168 = x_183;
goto lbl_169;
}
else
{
obj* x_187; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_93);
x_187 = lean::cnstr_get(x_178, 0);
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*1);
if (lean::is_exclusive(x_178)) {
 x_190 = x_178;
} else {
 lean::inc(x_187);
 lean::dec(x_178);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_187);
lean::cnstr_set_scalar(x_191, sizeof(void*)*1, x_189);
x_192 = x_191;
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_192);
x_194 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_193);
x_195 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_194);
return x_195;
}
}
else
{
obj* x_197; uint8 x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_93);
x_197 = lean::cnstr_get(x_171, 0);
x_199 = lean::cnstr_get_scalar<uint8>(x_171, sizeof(void*)*1);
if (lean::is_exclusive(x_171)) {
 x_200 = x_171;
} else {
 lean::inc(x_197);
 lean::dec(x_171);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_197);
lean::cnstr_set_scalar(x_201, sizeof(void*)*1, x_199);
x_202 = x_201;
x_203 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_202);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_203);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_204);
return x_205;
}
lbl_169:
{
obj* x_206; obj* x_207; 
x_206 = l_list_repr___main___rarg___closed__3;
x_207 = l_lean_ir_symbol(x_206, x_167);
if (lean::obj_tag(x_207) == 0)
{
obj* x_208; obj* x_210; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
x_208 = lean::cnstr_get(x_207, 1);
x_210 = lean::cnstr_get(x_207, 2);
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_212 = x_207;
} else {
 lean::inc(x_208);
 lean::inc(x_210);
 lean::dec(x_207);
 x_212 = lean::box(0);
}
x_213 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_212)) {
 x_214 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_214 = x_212;
}
lean::cnstr_set(x_214, 0, x_166);
lean::cnstr_set(x_214, 1, x_208);
lean::cnstr_set(x_214, 2, x_213);
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_210, x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_168, x_215);
if (lean::obj_tag(x_216) == 0)
{
obj* x_217; obj* x_219; obj* x_221; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
x_217 = lean::cnstr_get(x_216, 0);
x_219 = lean::cnstr_get(x_216, 1);
x_221 = lean::cnstr_get(x_216, 2);
if (lean::is_exclusive(x_216)) {
 x_223 = x_216;
} else {
 lean::inc(x_217);
 lean::inc(x_219);
 lean::inc(x_221);
 lean::dec(x_216);
 x_223 = lean::box(0);
}
x_224 = lean::apply_1(x_93, x_217);
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_224);
lean::cnstr_set(x_225, 1, x_219);
lean::cnstr_set(x_225, 2, x_213);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_221, x_225);
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_226);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_227);
x_229 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_228);
return x_229;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_93);
x_231 = lean::cnstr_get(x_216, 0);
x_233 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
if (lean::is_exclusive(x_216)) {
 x_234 = x_216;
} else {
 lean::inc(x_231);
 lean::dec(x_216);
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
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_236);
x_238 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_237);
x_239 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_238);
return x_239;
}
}
else
{
obj* x_241; uint8 x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; 
lean::dec(x_166);
x_241 = lean::cnstr_get(x_207, 0);
x_243 = lean::cnstr_get_scalar<uint8>(x_207, sizeof(void*)*1);
if (lean::is_exclusive(x_207)) {
 x_244 = x_207;
} else {
 lean::inc(x_241);
 lean::dec(x_207);
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
x_247 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_168, x_246);
if (lean::obj_tag(x_247) == 0)
{
obj* x_248; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_248 = lean::cnstr_get(x_247, 0);
x_250 = lean::cnstr_get(x_247, 1);
x_252 = lean::cnstr_get(x_247, 2);
if (lean::is_exclusive(x_247)) {
 x_254 = x_247;
} else {
 lean::inc(x_248);
 lean::inc(x_250);
 lean::inc(x_252);
 lean::dec(x_247);
 x_254 = lean::box(0);
}
x_255 = lean::apply_1(x_93, x_248);
x_256 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_254)) {
 x_257 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_257 = x_254;
}
lean::cnstr_set(x_257, 0, x_255);
lean::cnstr_set(x_257, 1, x_250);
lean::cnstr_set(x_257, 2, x_256);
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_252, x_257);
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_258);
x_260 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_259);
x_261 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_260);
return x_261;
}
else
{
obj* x_263; uint8 x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
lean::dec(x_93);
x_263 = lean::cnstr_get(x_247, 0);
x_265 = lean::cnstr_get_scalar<uint8>(x_247, sizeof(void*)*1);
if (lean::is_exclusive(x_247)) {
 x_266 = x_247;
} else {
 lean::inc(x_263);
 lean::dec(x_247);
 x_266 = lean::box(0);
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_263);
lean::cnstr_set_scalar(x_267, sizeof(void*)*1, x_265);
x_268 = x_267;
x_269 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_268);
x_270 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_42, x_269);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_270);
return x_271;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
x_10 = l_lean_ir_parse__phi(x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 2);
lean::inc(x_15);
lean::dec(x_10);
x_18 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_19 = l_lean_ir_symbol(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_19, 1);
x_22 = lean::cnstr_get(x_19, 2);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_33; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 2);
lean::inc(x_33);
lean::dec(x_28);
x_6 = x_29;
x_7 = x_31;
x_8 = x_33;
goto lbl_9;
}
else
{
obj* x_37; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
x_37 = lean::cnstr_get(x_28, 0);
x_39 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_exclusive(x_28)) {
 x_40 = x_28;
} else {
 lean::inc(x_37);
 lean::dec(x_28);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = x_41;
return x_42;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_11);
x_44 = lean::cnstr_get(x_19, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_47 = x_19;
} else {
 lean::inc(x_44);
 lean::dec(x_19);
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
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_49);
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
x_6 = x_51;
x_7 = x_53;
x_8 = x_55;
goto lbl_9;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_5);
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
return x_64;
}
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_5);
x_66 = lean::cnstr_get(x_10, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_69 = x_10;
} else {
 lean::inc(x_66);
 lean::dec(x_10);
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
return x_71;
}
lbl_9:
{
obj* x_73; obj* x_75; 
lean::inc(x_7);
x_73 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_5, x_7);
lean::dec(x_5);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; 
lean::dec(x_7);
x_78 = lean::box(0);
x_75 = x_78;
goto lbl_76;
}
else
{
obj* x_79; uint8 x_81; 
x_79 = lean::cnstr_get(x_73, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (x_81 == 0)
{
obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_73);
x_83 = lean::box(0);
x_84 = lean::cnstr_get(x_79, 2);
lean::inc(x_84);
lean::dec(x_79);
x_87 = l_mjoin___rarg___closed__1;
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_88, 0, x_84);
lean::closure_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_6);
lean::cnstr_set(x_89, 1, x_83);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_90, 0, x_88);
lean::closure_set(x_90, 1, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_92, 0, x_89);
lean::cnstr_set(x_92, 1, x_7);
lean::cnstr_set(x_92, 2, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_92);
return x_93;
}
else
{
obj* x_96; 
lean::dec(x_79);
lean::dec(x_7);
x_96 = lean::box(0);
x_75 = x_96;
goto lbl_76;
}
}
lbl_76:
{
lean::dec(x_75);
if (lean::obj_tag(x_73) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_98 = lean::cnstr_get(x_73, 0);
x_100 = lean::cnstr_get(x_73, 1);
x_102 = lean::cnstr_get(x_73, 2);
if (lean::is_exclusive(x_73)) {
 x_104 = x_73;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_73);
 x_104 = lean::box(0);
}
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_6);
lean::cnstr_set(x_105, 1, x_98);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_104)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_104;
}
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_100);
lean::cnstr_set(x_107, 2, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_108);
return x_109;
}
else
{
obj* x_111; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_6);
x_111 = lean::cnstr_get(x_73, 0);
x_113 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_exclusive(x_73)) {
 x_114 = x_73;
} else {
 lean::inc(x_111);
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
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_116);
return x_117;
}
}
}
}
else
{
obj* x_118; 
x_118 = l_lean_ir_parse__phi(x_1);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_118, 2);
lean::inc(x_123);
lean::dec(x_118);
x_126 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_127 = l_lean_ir_symbol(x_126, x_121);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_128 = lean::cnstr_get(x_127, 1);
x_130 = lean::cnstr_get(x_127, 2);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 x_132 = x_127;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
x_133 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_119);
lean::cnstr_set(x_134, 1, x_128);
lean::cnstr_set(x_134, 2, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_130, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_137 = lean::cnstr_get(x_136, 0);
x_139 = lean::cnstr_get(x_136, 1);
x_141 = lean::cnstr_get(x_136, 2);
if (lean::is_exclusive(x_136)) {
 x_143 = x_136;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_136);
 x_143 = lean::box(0);
}
x_144 = lean::box(0);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_137);
lean::cnstr_set(x_145, 1, x_144);
if (lean::is_scalar(x_143)) {
 x_146 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_146 = x_143;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_139);
lean::cnstr_set(x_146, 2, x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_141, x_146);
return x_147;
}
else
{
obj* x_148; uint8 x_150; obj* x_151; obj* x_152; obj* x_153; 
x_148 = lean::cnstr_get(x_136, 0);
x_150 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
if (lean::is_exclusive(x_136)) {
 x_151 = x_136;
} else {
 lean::inc(x_148);
 lean::dec(x_136);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_148);
lean::cnstr_set_scalar(x_152, sizeof(void*)*1, x_150);
x_153 = x_152;
return x_153;
}
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_119);
x_155 = lean::cnstr_get(x_127, 0);
x_157 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
if (lean::is_exclusive(x_127)) {
 x_158 = x_127;
} else {
 lean::inc(x_155);
 lean::dec(x_127);
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
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_164; obj* x_166; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_162 = lean::cnstr_get(x_161, 0);
x_164 = lean::cnstr_get(x_161, 1);
x_166 = lean::cnstr_get(x_161, 2);
if (lean::is_exclusive(x_161)) {
 x_168 = x_161;
} else {
 lean::inc(x_162);
 lean::inc(x_164);
 lean::inc(x_166);
 lean::dec(x_161);
 x_168 = lean::box(0);
}
x_169 = lean::box(0);
x_170 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_170, 0, x_162);
lean::cnstr_set(x_170, 1, x_169);
x_171 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_168)) {
 x_172 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_172 = x_168;
}
lean::cnstr_set(x_172, 0, x_170);
lean::cnstr_set(x_172, 1, x_164);
lean::cnstr_set(x_172, 2, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_172);
return x_173;
}
else
{
obj* x_174; uint8 x_176; obj* x_177; obj* x_178; obj* x_179; 
x_174 = lean::cnstr_get(x_161, 0);
x_176 = lean::cnstr_get_scalar<uint8>(x_161, sizeof(void*)*1);
if (lean::is_exclusive(x_161)) {
 x_177 = x_161;
} else {
 lean::inc(x_174);
 lean::dec(x_161);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_174);
lean::cnstr_set_scalar(x_178, sizeof(void*)*1, x_176);
x_179 = x_178;
return x_179;
}
}
}
else
{
obj* x_180; uint8 x_182; obj* x_183; obj* x_184; obj* x_185; 
x_180 = lean::cnstr_get(x_118, 0);
x_182 = lean::cnstr_get_scalar<uint8>(x_118, sizeof(void*)*1);
if (lean::is_exclusive(x_118)) {
 x_183 = x_118;
} else {
 lean::inc(x_180);
 lean::dec(x_118);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_180);
lean::cnstr_set_scalar(x_184, sizeof(void*)*1, x_182);
x_185 = x_184;
return x_185;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
x_10 = l_lean_ir_parse__instr(x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 2);
lean::inc(x_15);
lean::dec(x_10);
x_18 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_19 = l_lean_ir_symbol(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_19, 1);
x_22 = lean::cnstr_get(x_19, 2);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_33; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 2);
lean::inc(x_33);
lean::dec(x_28);
x_6 = x_29;
x_7 = x_31;
x_8 = x_33;
goto lbl_9;
}
else
{
obj* x_37; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_5);
x_37 = lean::cnstr_get(x_28, 0);
x_39 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_exclusive(x_28)) {
 x_40 = x_28;
} else {
 lean::inc(x_37);
 lean::dec(x_28);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = x_41;
return x_42;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_11);
x_44 = lean::cnstr_get(x_19, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_47 = x_19;
} else {
 lean::inc(x_44);
 lean::dec(x_19);
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
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_49);
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
x_6 = x_51;
x_7 = x_53;
x_8 = x_55;
goto lbl_9;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_5);
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
return x_64;
}
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_5);
x_66 = lean::cnstr_get(x_10, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_69 = x_10;
} else {
 lean::inc(x_66);
 lean::dec(x_10);
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
return x_71;
}
lbl_9:
{
obj* x_73; obj* x_75; 
lean::inc(x_7);
x_73 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(x_5, x_7);
lean::dec(x_5);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; 
lean::dec(x_7);
x_78 = lean::box(0);
x_75 = x_78;
goto lbl_76;
}
else
{
obj* x_79; uint8 x_81; 
x_79 = lean::cnstr_get(x_73, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (x_81 == 0)
{
obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_73);
x_83 = lean::box(0);
x_84 = lean::cnstr_get(x_79, 2);
lean::inc(x_84);
lean::dec(x_79);
x_87 = l_mjoin___rarg___closed__1;
x_88 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_88, 0, x_84);
lean::closure_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_6);
lean::cnstr_set(x_89, 1, x_83);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_90, 0, x_88);
lean::closure_set(x_90, 1, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_92, 0, x_89);
lean::cnstr_set(x_92, 1, x_7);
lean::cnstr_set(x_92, 2, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_92);
return x_93;
}
else
{
obj* x_96; 
lean::dec(x_79);
lean::dec(x_7);
x_96 = lean::box(0);
x_75 = x_96;
goto lbl_76;
}
}
lbl_76:
{
lean::dec(x_75);
if (lean::obj_tag(x_73) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_98 = lean::cnstr_get(x_73, 0);
x_100 = lean::cnstr_get(x_73, 1);
x_102 = lean::cnstr_get(x_73, 2);
if (lean::is_exclusive(x_73)) {
 x_104 = x_73;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_73);
 x_104 = lean::box(0);
}
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_6);
lean::cnstr_set(x_105, 1, x_98);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_104)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_104;
}
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_100);
lean::cnstr_set(x_107, 2, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_108);
return x_109;
}
else
{
obj* x_111; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_6);
x_111 = lean::cnstr_get(x_73, 0);
x_113 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_exclusive(x_73)) {
 x_114 = x_73;
} else {
 lean::inc(x_111);
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
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_116);
return x_117;
}
}
}
}
else
{
obj* x_118; 
x_118 = l_lean_ir_parse__instr(x_1);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_118, 2);
lean::inc(x_123);
lean::dec(x_118);
x_126 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_127 = l_lean_ir_symbol(x_126, x_121);
if (lean::obj_tag(x_127) == 0)
{
obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_128 = lean::cnstr_get(x_127, 1);
x_130 = lean::cnstr_get(x_127, 2);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 x_132 = x_127;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_127);
 x_132 = lean::box(0);
}
x_133 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_132)) {
 x_134 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_134 = x_132;
}
lean::cnstr_set(x_134, 0, x_119);
lean::cnstr_set(x_134, 1, x_128);
lean::cnstr_set(x_134, 2, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_130, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_137 = lean::cnstr_get(x_136, 0);
x_139 = lean::cnstr_get(x_136, 1);
x_141 = lean::cnstr_get(x_136, 2);
if (lean::is_exclusive(x_136)) {
 x_143 = x_136;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_136);
 x_143 = lean::box(0);
}
x_144 = lean::box(0);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_137);
lean::cnstr_set(x_145, 1, x_144);
if (lean::is_scalar(x_143)) {
 x_146 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_146 = x_143;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_139);
lean::cnstr_set(x_146, 2, x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_141, x_146);
return x_147;
}
else
{
obj* x_148; uint8 x_150; obj* x_151; obj* x_152; obj* x_153; 
x_148 = lean::cnstr_get(x_136, 0);
x_150 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
if (lean::is_exclusive(x_136)) {
 x_151 = x_136;
} else {
 lean::inc(x_148);
 lean::dec(x_136);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_148);
lean::cnstr_set_scalar(x_152, sizeof(void*)*1, x_150);
x_153 = x_152;
return x_153;
}
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_119);
x_155 = lean::cnstr_get(x_127, 0);
x_157 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
if (lean::is_exclusive(x_127)) {
 x_158 = x_127;
} else {
 lean::inc(x_155);
 lean::dec(x_127);
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
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_160);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_164; obj* x_166; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_162 = lean::cnstr_get(x_161, 0);
x_164 = lean::cnstr_get(x_161, 1);
x_166 = lean::cnstr_get(x_161, 2);
if (lean::is_exclusive(x_161)) {
 x_168 = x_161;
} else {
 lean::inc(x_162);
 lean::inc(x_164);
 lean::inc(x_166);
 lean::dec(x_161);
 x_168 = lean::box(0);
}
x_169 = lean::box(0);
x_170 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_170, 0, x_162);
lean::cnstr_set(x_170, 1, x_169);
x_171 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_168)) {
 x_172 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_172 = x_168;
}
lean::cnstr_set(x_172, 0, x_170);
lean::cnstr_set(x_172, 1, x_164);
lean::cnstr_set(x_172, 2, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_172);
return x_173;
}
else
{
obj* x_174; uint8 x_176; obj* x_177; obj* x_178; obj* x_179; 
x_174 = lean::cnstr_get(x_161, 0);
x_176 = lean::cnstr_get_scalar<uint8>(x_161, sizeof(void*)*1);
if (lean::is_exclusive(x_161)) {
 x_177 = x_161;
} else {
 lean::inc(x_174);
 lean::dec(x_161);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_174);
lean::cnstr_set_scalar(x_178, sizeof(void*)*1, x_176);
x_179 = x_178;
return x_179;
}
}
}
else
{
obj* x_180; uint8 x_182; obj* x_183; obj* x_184; obj* x_185; 
x_180 = lean::cnstr_get(x_118, 0);
x_182 = lean::cnstr_get_scalar<uint8>(x_118, sizeof(void*)*1);
if (lean::is_exclusive(x_118)) {
 x_183 = x_118;
} else {
 lean::inc(x_180);
 lean::dec(x_118);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_180);
lean::cnstr_set_scalar(x_184, sizeof(void*)*1, x_182);
x_185 = x_184;
return x_185;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__5(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_lean_ir_parse__typed__assignment___closed__1;
x_14 = l_lean_ir_symbol(x_13, x_8);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 1);
x_17 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_19 = x_14;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_14);
 x_19 = lean::box(0);
}
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_19;
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
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_6);
x_39 = lean::cnstr_get(x_14, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_42 = x_14;
} else {
 lean::inc(x_39);
 lean::dec(x_14);
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
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_44);
x_46 = l_lean_parser_parsec__t_try__mk__res___rarg(x_45);
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
obj* x_60; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; 
x_60 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_62 = x_5;
} else {
 lean::inc(x_60);
 lean::dec(x_5);
 x_62 = lean::box(0);
}
x_63 = 0;
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_63);
x_65 = x_64;
return x_65;
}
lbl_4:
{
obj* x_66; 
x_66 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(x_2);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_71; obj* x_74; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(x_69);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_82; 
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_74, 2);
lean::inc(x_79);
lean::dec(x_74);
x_82 = l_lean_ir_parse__terminator(x_77);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_90; obj* x_91; 
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_82, 2);
lean::inc(x_87);
lean::dec(x_82);
x_90 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_91 = l_lean_ir_symbol(x_90, x_85);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_91, 1);
x_94 = lean::cnstr_get(x_91, 2);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 x_96 = x_91;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_91);
 x_96 = lean::box(0);
}
x_97 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_83);
lean::cnstr_set(x_98, 1, x_92);
lean::cnstr_set(x_98, 2, x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_98);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_99);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; obj* x_103; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_101 = lean::cnstr_get(x_100, 0);
x_103 = lean::cnstr_get(x_100, 1);
x_105 = lean::cnstr_get(x_100, 2);
if (lean::is_exclusive(x_100)) {
 x_107 = x_100;
} else {
 lean::inc(x_101);
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_100);
 x_107 = lean::box(0);
}
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_1);
lean::cnstr_set(x_108, 1, x_67);
lean::cnstr_set(x_108, 2, x_75);
lean::cnstr_set(x_108, 3, x_101);
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_103);
lean::cnstr_set(x_109, 2, x_97);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_111);
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_112);
return x_113;
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_75);
lean::dec(x_1);
lean::dec(x_67);
x_117 = lean::cnstr_get(x_100, 0);
x_119 = lean::cnstr_get_scalar<uint8>(x_100, sizeof(void*)*1);
if (lean::is_exclusive(x_100)) {
 x_120 = x_100;
} else {
 lean::inc(x_117);
 lean::dec(x_100);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = x_121;
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_122);
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_123);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_124);
return x_125;
}
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
lean::dec(x_83);
x_127 = lean::cnstr_get(x_91, 0);
x_129 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (lean::is_exclusive(x_91)) {
 x_130 = x_91;
} else {
 lean::inc(x_127);
 lean::dec(x_91);
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
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_132);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_136; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_134 = lean::cnstr_get(x_133, 0);
x_136 = lean::cnstr_get(x_133, 1);
x_138 = lean::cnstr_get(x_133, 2);
if (lean::is_exclusive(x_133)) {
 x_140 = x_133;
} else {
 lean::inc(x_134);
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_133);
 x_140 = lean::box(0);
}
x_141 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_141, 0, x_1);
lean::cnstr_set(x_141, 1, x_67);
lean::cnstr_set(x_141, 2, x_75);
lean::cnstr_set(x_141, 3, x_134);
x_142 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_140)) {
 x_143 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_143 = x_140;
}
lean::cnstr_set(x_143, 0, x_141);
lean::cnstr_set(x_143, 1, x_136);
lean::cnstr_set(x_143, 2, x_142);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_138, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_146);
return x_147;
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_75);
lean::dec(x_1);
lean::dec(x_67);
x_151 = lean::cnstr_get(x_133, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_133, sizeof(void*)*1);
if (lean::is_exclusive(x_133)) {
 x_154 = x_133;
} else {
 lean::inc(x_151);
 lean::dec(x_133);
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
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_156);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_157);
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_158);
return x_159;
}
}
}
else
{
obj* x_163; uint8 x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_75);
lean::dec(x_1);
lean::dec(x_67);
x_163 = lean::cnstr_get(x_82, 0);
x_165 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_exclusive(x_82)) {
 x_166 = x_82;
} else {
 lean::inc(x_163);
 lean::dec(x_82);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_163);
lean::cnstr_set_scalar(x_167, sizeof(void*)*1, x_165);
x_168 = x_167;
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_168);
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_169);
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_170);
return x_171;
}
}
else
{
obj* x_174; uint8 x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
lean::dec(x_1);
lean::dec(x_67);
x_174 = lean::cnstr_get(x_74, 0);
x_176 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_177 = x_74;
} else {
 lean::inc(x_174);
 lean::dec(x_74);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_174);
lean::cnstr_set_scalar(x_178, sizeof(void*)*1, x_176);
x_179 = x_178;
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_179);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_180);
return x_181;
}
}
else
{
obj* x_183; uint8 x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
lean::dec(x_1);
x_183 = lean::cnstr_get(x_66, 0);
x_185 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_186 = x_66;
} else {
 lean::inc(x_183);
 lean::dec(x_66);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_183);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_185);
x_188 = x_187;
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_188);
return x_189;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
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
obj* x_35; obj* x_37; obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_35 = lean::cnstr_get(x_34, 1);
x_37 = lean::cnstr_get(x_34, 2);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_39 = x_34;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_34);
 x_39 = lean::box(0);
}
x_40 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_40, 0, x_9);
x_41 = lean::unbox(x_26);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_41);
x_42 = x_40;
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_39;
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
obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_9);
lean::dec(x_26);
x_52 = lean::cnstr_get(x_34, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
if (lean::is_exclusive(x_34)) {
 x_55 = x_34;
} else {
 lean::inc(x_52);
 lean::dec(x_34);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*1, x_54);
x_57 = x_56;
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_60);
return x_61;
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_9);
x_63 = lean::cnstr_get(x_25, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (lean::is_exclusive(x_25)) {
 x_66 = x_25;
} else {
 lean::inc(x_63);
 lean::dec(x_25);
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
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_70);
return x_71;
}
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_9);
x_73 = lean::cnstr_get(x_17, 0);
x_75 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 x_76 = x_17;
} else {
 lean::inc(x_73);
 lean::dec(x_17);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_75);
x_78 = x_77;
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_79);
return x_80;
}
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_81 = lean::cnstr_get(x_8, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_84 = x_8;
} else {
 lean::inc(x_81);
 lean::dec(x_8);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_86);
return x_87;
}
}
else
{
obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; 
x_88 = lean::cnstr_get(x_2, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_91 = x_2;
} else {
 lean::inc(x_88);
 lean::dec(x_2);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
return x_93;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__arg(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__header___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
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
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_lean_ir_parse__typed__assignment___closed__2;
x_27 = l_lean_ir_str2type;
x_28 = l_lean_ir_parse__key2val___main___rarg(x_26, x_27, x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_29 = lean::cnstr_get(x_28, 0);
x_31 = lean::cnstr_get(x_28, 1);
x_33 = lean::cnstr_get(x_28, 2);
if (lean::is_exclusive(x_28)) {
 x_35 = x_28;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_28);
 x_35 = lean::box(0);
}
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set(x_37, 1, x_31);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_37);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_40 = lean::cnstr_get(x_39, 0);
x_42 = lean::cnstr_get(x_39, 1);
x_44 = lean::cnstr_get(x_39, 2);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_47, 0, x_3);
lean::cnstr_set(x_47, 1, x_10);
lean::cnstr_set(x_47, 2, x_40);
lean::cnstr_set_scalar(x_47, sizeof(void*)*3, x_0);
x_48 = x_47;
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_46;
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
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_3);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_39, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 x_58 = x_39;
} else {
 lean::inc(x_55);
 lean::dec(x_39);
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
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_61);
return x_62;
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_28, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_exclusive(x_28)) {
 x_66 = x_28;
} else {
 lean::inc(x_63);
 lean::dec(x_28);
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
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_70 = lean::cnstr_get(x_69, 0);
x_72 = lean::cnstr_get(x_69, 1);
x_74 = lean::cnstr_get(x_69, 2);
if (lean::is_exclusive(x_69)) {
 x_76 = x_69;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_69);
 x_76 = lean::box(0);
}
x_77 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_77, 0, x_3);
lean::cnstr_set(x_77, 1, x_10);
lean::cnstr_set(x_77, 2, x_70);
lean::cnstr_set_scalar(x_77, sizeof(void*)*3, x_0);
x_78 = x_77;
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_76)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_76;
}
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_72);
lean::cnstr_set(x_80, 2, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_82);
return x_83;
}
else
{
obj* x_86; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_3);
lean::dec(x_10);
x_86 = lean::cnstr_get(x_69, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_89 = x_69;
} else {
 lean::inc(x_86);
 lean::dec(x_69);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_86);
lean::cnstr_set_scalar(x_90, sizeof(void*)*1, x_88);
x_91 = x_90;
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_92);
return x_93;
}
}
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_3);
lean::dec(x_10);
x_96 = lean::cnstr_get(x_20, 0);
x_98 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_99 = x_20;
} else {
 lean::inc(x_96);
 lean::dec(x_20);
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
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_102);
return x_103;
}
}
lbl_15:
{
obj* x_105; 
lean::dec(x_14);
x_105 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__header___spec__1(x_5);
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
x_10 = x_106;
x_11 = x_108;
x_12 = x_110;
goto lbl_13;
}
else
{
obj* x_114; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_3);
x_114 = lean::cnstr_get(x_105, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (lean::is_exclusive(x_105)) {
 x_117 = x_105;
} else {
 lean::inc(x_114);
 lean::dec(x_105);
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
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_119);
return x_120;
}
}
}
else
{
obj* x_121; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; 
x_121 = lean::cnstr_get(x_2, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_124 = x_2;
} else {
 lean::inc(x_121);
 lean::dec(x_2);
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
return x_126;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_7; obj* x_9; uint8 x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_12 = 0;
x_13 = l_lean_ir_parse__header(x_12, x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_13, 0);
x_16 = lean::cnstr_get(x_13, 1);
x_18 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_20 = x_13;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_14);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_20;
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
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_13, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_42 = x_13;
} else {
 lean::inc(x_39);
 lean::dec(x_13);
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
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_50; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 2);
lean::inc(x_50);
lean::dec(x_45);
x_1 = x_46;
x_2 = x_48;
x_3 = x_50;
goto lbl_4;
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_45, 0);
x_55 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 x_56 = x_45;
} else {
 lean::inc(x_53);
 lean::dec(x_45);
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
return x_58;
}
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_6, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_62 = x_6;
} else {
 lean::inc(x_59);
 lean::dec(x_6);
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
return x_64;
}
lbl_4:
{
obj* x_65; obj* x_66; 
x_65 = l_lean_ir_parse__typed__assignment___closed__3;
x_66 = l_lean_ir_symbol(x_65, x_2);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_72; obj* x_73; 
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(x_67);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_74 = lean::cnstr_get(x_73, 0);
x_76 = lean::cnstr_get(x_73, 1);
x_78 = lean::cnstr_get(x_73, 2);
if (lean::is_exclusive(x_73)) {
 x_80 = x_73;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
x_81 = lean::apply_1(x_1, x_74);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_80)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_80;
}
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_76);
lean::cnstr_set(x_83, 2, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_84);
return x_85;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_1);
x_87 = lean::cnstr_get(x_73, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_exclusive(x_73)) {
 x_90 = x_73;
} else {
 lean::inc(x_87);
 lean::dec(x_73);
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
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_92);
return x_93;
}
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_1);
x_95 = lean::cnstr_get(x_66, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_98 = x_66;
} else {
 lean::inc(x_95);
 lean::dec(x_66);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_100);
return x_101;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
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
lean::inc(x_7);
x_15 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_21; 
lean::dec(x_11);
lean::dec(x_7);
x_21 = lean::box(0);
x_17 = x_21;
goto lbl_18;
}
else
{
obj* x_22; uint8 x_24; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_15);
x_26 = lean::box(0);
x_27 = lean::cnstr_get(x_22, 2);
lean::inc(x_27);
lean::dec(x_22);
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
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_7);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_35);
return x_36;
}
else
{
obj* x_40; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_22);
x_40 = lean::box(0);
x_17 = x_40;
goto lbl_18;
}
}
lbl_18:
{
lean::dec(x_17);
if (lean::obj_tag(x_15) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_15, 0);
x_44 = lean::cnstr_get(x_15, 1);
x_46 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_48 = x_15;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_15);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_42);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_48;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_52);
return x_53;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_5);
x_55 = lean::cnstr_get(x_15, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_58 = x_15;
} else {
 lean::inc(x_55);
 lean::dec(x_15);
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
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
return x_67;
}
}
else
{
obj* x_68; 
x_68 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
x_73 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 x_75 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_68);
 x_75 = lean::box(0);
}
x_76 = lean::box(0);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_69);
lean::cnstr_set(x_77, 1, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_71);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_79);
return x_80;
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_68, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_84 = x_68;
} else {
 lean::inc(x_81);
 lean::dec(x_68);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
return x_86;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_1, x_0);
lean::dec(x_1);
x_4 = l_lean_ir_keyword___closed__1;
x_5 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_4, x_2);
return x_5;
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
obj* x_7; obj* x_9; uint8 x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_12 = 1;
x_13 = l_lean_ir_parse__header(x_12, x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_13, 0);
x_16 = lean::cnstr_get(x_13, 1);
x_18 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_20 = x_13;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_14);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_20;
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
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_13, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_42 = x_13;
} else {
 lean::inc(x_39);
 lean::dec(x_13);
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
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_50; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_45, 2);
lean::inc(x_50);
lean::dec(x_45);
x_1 = x_46;
x_2 = x_48;
x_3 = x_50;
goto lbl_4;
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_45, 0);
x_55 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 x_56 = x_45;
} else {
 lean::inc(x_53);
 lean::dec(x_45);
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
return x_58;
}
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_6, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_62 = x_6;
} else {
 lean::inc(x_59);
 lean::dec(x_6);
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
return x_64;
}
lbl_4:
{
obj* x_65; obj* x_66; 
x_65 = l_lean_ir_parse__typed__assignment___closed__3;
x_66 = l_lean_ir_symbol(x_65, x_2);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_72; obj* x_73; 
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(x_67);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_74 = lean::cnstr_get(x_73, 0);
x_76 = lean::cnstr_get(x_73, 1);
x_78 = lean::cnstr_get(x_73, 2);
if (lean::is_exclusive(x_73)) {
 x_80 = x_73;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
x_81 = lean::apply_1(x_1, x_74);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_80)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_80;
}
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_76);
lean::cnstr_set(x_83, 2, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_84);
return x_85;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_1);
x_87 = lean::cnstr_get(x_73, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_exclusive(x_73)) {
 x_90 = x_73;
} else {
 lean::inc(x_87);
 lean::dec(x_73);
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
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_92);
return x_93;
}
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_1);
x_95 = lean::cnstr_get(x_66, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_98 = x_66;
} else {
 lean::inc(x_95);
 lean::dec(x_66);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_100);
return x_101;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_3; obj* x_5; uint8 x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = 0;
x_9 = l_lean_ir_parse__header(x_8, x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
x_14 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_16;
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
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_25 = x_9;
} else {
 lean::inc(x_22);
 lean::dec(x_9);
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
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_27);
return x_28;
}
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_2, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_32 = x_2;
} else {
 lean::inc(x_29);
 lean::dec(x_2);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
return x_34;
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
