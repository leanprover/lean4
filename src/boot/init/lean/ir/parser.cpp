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
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4___boxed(obj*);
namespace lean {
obj* nat2int(obj*);
}
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__arg(obj*);
uint8 l_char_is__whitespace(uint32);
obj* l_lean_ir_parse__var___boxed(obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_ir_parse__key2val___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9___boxed(obj*, obj*);
obj* l_lean_ir_str2abinop;
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(obj*, obj*);
obj* l_lean_ir_parse__assignment___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1___boxed(obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7___boxed(obj*);
obj* l_lean_ir_parse__type(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6(obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1___boxed(obj*);
extern obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(obj*);
obj* l_lean_parser_parse__string__literal___at_lean_ir_parse__literal___spec__1(obj*);
obj* l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3___boxed(obj*);
obj* l_lean_parser_monad__parsec_sep__by1___rarg___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_ir_parse__key2val___main___boxed(obj*);
extern uint32 l_lean_id__end__escape;
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_symbol___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1___boxed(obj*);
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
obj* l_lean_ir_parse__instr___lambda__4___boxed(obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1___boxed(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__6(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5___boxed(obj*, obj*);
obj* l_lean_ir_identifier___boxed(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__header___spec__3___boxed(obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3___boxed(obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
obj* l_lean_ir_parse__instr___lambda__3(obj*, uint16, obj*);
obj* l_lean_ir_parse__assign__binop(obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_parse__var___closed__1;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_ir_parse__defconst(obj*);
obj* l_lean_ir_parse__phi___boxed(obj*);
obj* l_lean_ir_parse__assignment(obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__5(uint32, obj*);
obj* l_lean_ir_parse__header___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__6(obj*, obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__3;
namespace lean {
uint16 uint16_of_nat(obj*);
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1___boxed(obj*);
obj* l_lean_ir_parse__untyped__assignment___closed__5;
obj* l_lean_ir_parse__typed__assignment___closed__3;
obj* l_lean_ir_parse__fnid___boxed(obj*);
obj* l_lean_ir_parse__key2val___main___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_ir_str2type;
obj* l_lean_ir_parse__usize(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_parse__literal(obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__16(obj*, obj*, obj*);
obj* l_string_to__nat(obj*);
obj* l_lean_ir_parse__block___boxed(obj*);
obj* l_lean_ir_parse__key2val___boxed(obj*);
obj* l_lean_ir_parse__instr___closed__3;
obj* l_lean_ir_parse__typed__assignment(obj*, obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_ir_parse__instr___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(obj*, obj*);
obj* l_lean_parser_id__part___at_lean_ir_identifier___spec__2___boxed(obj*);
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
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2___boxed(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_ir_parse__literal___spec__5(obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_ir_parse__literal___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_identifier___spec__14(obj*, obj*, obj*);
obj* l_lean_ir_parse__block(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_symbol___spec__4(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__6___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__6___boxed(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_ir_parse__var(obj*);
obj* l_lean_ir_parse__terminator(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2___boxed(obj*);
obj* l_lean_ir_parse__terminator___closed__2;
obj* l_lean_parser_monad__parsec_take__while1___at_lean_ir_parse__literal___spec__10(obj*);
obj* l_lean_ir_parse__typed__assignment___lambda__1(obj*, uint8, uint8, obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__header___spec__1(obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(obj*);
obj* l_lean_ir_parse__blockid___boxed(obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_ir_identifier___spec__19(obj*, obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__4(obj*, obj*, obj*);
obj* l_lean_ir_parse__fnid(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__4___boxed(obj*, obj*, obj*);
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
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1___boxed(obj*);
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
obj* l_lean_ir_parse__def___lambda__1___boxed(obj*, obj*);
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
obj* l_lean_ir_parse__terminator___lambda__1___boxed(obj*, obj*);
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
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_parse__uint16___closed__2;
obj* l_lean_ir_parse__untyped__assignment___lambda__2(obj*, obj*, obj*);
obj* l_lean_ir_parse__external(obj*);
obj* l_lean_ir_parse__untyped__assignment___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1(obj*);
obj* l_lean_ir_parse__external___closed__1;
obj* l_lean_ir_parse__key2val___main(obj*);
obj* l_lean_ir_parse__key2val___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6___boxed(obj*);
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
lean::dec(x_2);
return x_7;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__whitespace(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
lean::dec(x_2);
return x_12;
}
else
{
obj* x_14; obj* x_15; obj* x_17; uint8 x_18; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_0);
x_17 = lean::string_iterator_next(x_2);
x_18 = 1;
x_0 = x_15;
x_1 = x_18;
x_2 = x_17;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
lean::dec(x_2);
return x_21;
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
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_char_has__repr___closed__1;
x_6 = lean::string_append(x_5, x_0);
x_7 = lean::string_append(x_6, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(x_0, x_4, x_1);
lean::dec(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_9, 2);
lean::inc(x_13);
lean::dec(x_9);
x_16 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_11);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_16);
x_18 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_17, x_8);
lean::dec(x_8);
return x_18;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_9, 0);
x_22 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_23 = x_9;
} else {
 lean::inc(x_20);
 lean::dec(x_9);
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
x_26 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_25, x_8);
lean::dec(x_8);
return x_26;
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_char_has__repr___closed__1;
x_6 = lean::string_append(x_5, x_0);
x_7 = lean::string_append(x_6, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_ir_symbol___spec__1(x_0, x_4, x_1);
lean::dec(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_11 = lean::cnstr_get(x_9, 1);
x_13 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_15 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::string_iterator_has_next(x_11);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::box(0);
x_18 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_11);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_21);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_28 = l_lean_parser_parsec__t_try__mk__res___rarg(x_27);
x_29 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_8);
lean::dec(x_8);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; 
x_31 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_33 = x_20;
} else {
 lean::inc(x_31);
 lean::dec(x_20);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_31, 3);
lean::inc(x_38);
lean::dec(x_31);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_34);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_8);
lean::cnstr_set(x_41, 3, x_38);
x_42 = 0;
if (lean::is_scalar(x_33)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_33;
}
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_42);
x_44 = x_43;
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_11);
x_46 = l_lean_is__id__rest(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_47 = lean::box(0);
x_48 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_15)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_15;
}
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_11);
lean::cnstr_set(x_49, 2, x_48);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 2);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_51);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_56);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
x_59 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_8);
lean::dec(x_8);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; 
x_61 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_63 = x_50;
} else {
 lean::inc(x_61);
 lean::dec(x_50);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_61, 3);
lean::inc(x_68);
lean::dec(x_61);
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_64);
lean::cnstr_set(x_71, 1, x_66);
lean::cnstr_set(x_71, 2, x_8);
lean::cnstr_set(x_71, 3, x_68);
x_72 = 0;
if (lean::is_scalar(x_63)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_63;
}
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_72);
x_74 = x_73;
return x_74;
}
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_15);
x_76 = l_char_quote__core(x_45);
x_77 = lean::string_append(x_5, x_76);
lean::dec(x_76);
x_79 = lean::string_append(x_77, x_5);
x_80 = lean::box(0);
x_81 = l_mjoin___rarg___closed__1;
x_82 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_79, x_81, x_80, x_80, x_11);
lean::dec(x_11);
lean::dec(x_79);
x_85 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_82);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_88 = lean::cnstr_get(x_87, 1);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 2);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_88);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_93);
x_95 = l_lean_parser_parsec__t_try__mk__res___rarg(x_94);
x_96 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_95, x_8);
lean::dec(x_8);
return x_96;
}
else
{
obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_105; obj* x_108; uint8 x_109; obj* x_110; obj* x_111; 
x_98 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_100 = x_87;
} else {
 lean::inc(x_98);
 lean::dec(x_87);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_98, 3);
lean::inc(x_105);
lean::dec(x_98);
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_101);
lean::cnstr_set(x_108, 1, x_103);
lean::cnstr_set(x_108, 2, x_8);
lean::cnstr_set(x_108, 3, x_105);
x_109 = 0;
if (lean::is_scalar(x_100)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_100;
}
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_109);
x_111 = x_110;
return x_111;
}
}
}
}
else
{
obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_122; uint8 x_123; obj* x_124; obj* x_125; 
x_112 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_114 = x_9;
} else {
 lean::inc(x_112);
 lean::dec(x_9);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_112, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_112, 3);
lean::inc(x_119);
lean::dec(x_112);
x_122 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_122, 0, x_115);
lean::cnstr_set(x_122, 1, x_117);
lean::cnstr_set(x_122, 2, x_8);
lean::cnstr_set(x_122, 3, x_119);
x_123 = 0;
if (lean::is_scalar(x_114)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_114;
}
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_123);
x_125 = x_124;
return x_125;
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
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
lean::dec(x_9);
lean::dec(x_2);
return x_26;
}
else
{
obj* x_29; uint8 x_31; 
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_26);
x_33 = l_lean_ir_parse__key2val___main___rarg(x_0, x_9, x_2);
x_34 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_29, x_33);
return x_34;
}
else
{
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_29);
return x_26;
}
}
}
else
{
obj* x_39; uint8 x_41; obj* x_42; 
lean::dec(x_14);
x_39 = lean::cnstr_get(x_18, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_42 = x_18;
} else {
 lean::inc(x_39);
 lean::dec(x_18);
 x_42 = lean::box(0);
}
if (x_41 == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_42);
x_44 = l_lean_ir_parse__key2val___main___rarg(x_0, x_9, x_2);
x_45 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_44);
return x_45;
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_9);
lean::dec(x_2);
if (lean::is_scalar(x_42)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_42;
}
lean::cnstr_set(x_48, 0, x_39);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_41);
x_49 = x_48;
return x_49;
}
}
}
}
}
obj* l_lean_ir_parse__key2val___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_ir_parse__key2val___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__key2val___main___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__key2val___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_ir_parse__key2val___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__key2val___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
lean::dec(x_1);
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
lean::dec(x_1);
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
lean::dec(x_1);
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
lean::dec(x_1);
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
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; 
x_12 = l_char_quote__core(x_10);
x_13 = l_char_has__repr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_16, x_18, x_17, x_17, x_1);
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
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_15, x_17, x_16, x_16, x_0);
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
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_1);
x_5 = lean::box(0);
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_0, x_6, x_4, x_5, x_2);
lean::dec(x_4);
return x_7;
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
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_15, x_17, x_16, x_16, x_0);
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
obj* _init_l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
x_71 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_68, x_70, x_69, x_69, x_0);
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
x_80 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_77, x_79, x_78, x_78, x_0);
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
x_108 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_122 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_131 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_129, x_130, x_128, x_128, x_0);
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
x_145 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_142, x_144, x_143, x_143, x_0);
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
x_158 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_155, x_157, x_156, x_156, x_0);
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
x_168 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_165, x_167, x_166, x_166, x_0);
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
x_196 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_206 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
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
x_211 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7___closed__1;
x_212 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_210, x_211);
return x_212;
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
obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_37; 
x_31 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
x_32 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_31, x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_32);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_35);
return x_37;
}
else
{
obj* x_39; 
lean::dec(x_0);
x_39 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_5);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_47; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 2);
lean::inc(x_44);
lean::dec(x_39);
x_47 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_42);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_50; obj* x_52; obj* x_55; 
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 2);
lean::inc(x_52);
lean::dec(x_47);
x_55 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_50);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_60; obj* x_63; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_55, 2);
lean::inc(x_60);
lean::dec(x_55);
x_63 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_58);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_77; obj* x_79; obj* x_82; obj* x_84; uint32 x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_64 = lean::cnstr_get(x_63, 0);
x_66 = lean::cnstr_get(x_63, 1);
x_68 = lean::cnstr_get(x_63, 2);
if (lean::is_exclusive(x_63)) {
 x_70 = x_63;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_63);
 x_70 = lean::box(0);
}
x_71 = lean::mk_nat_obj(16u);
x_72 = lean::nat_mul(x_71, x_40);
lean::dec(x_40);
x_74 = lean::nat_add(x_72, x_48);
lean::dec(x_48);
lean::dec(x_72);
x_77 = lean::nat_mul(x_71, x_74);
lean::dec(x_74);
x_79 = lean::nat_add(x_77, x_56);
lean::dec(x_56);
lean::dec(x_77);
x_82 = lean::nat_mul(x_71, x_79);
lean::dec(x_79);
x_84 = lean::nat_add(x_82, x_64);
lean::dec(x_64);
lean::dec(x_82);
x_87 = l_char_of__nat(x_84);
lean::dec(x_84);
x_89 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_90 = lean::box_uint32(x_87);
if (lean::is_scalar(x_70)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_70;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_66);
lean::cnstr_set(x_91, 2, x_89);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_93);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_95);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_96);
return x_97;
}
else
{
obj* x_101; uint8 x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_56);
lean::dec(x_40);
lean::dec(x_48);
x_101 = lean::cnstr_get(x_63, 0);
x_103 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (lean::is_exclusive(x_63)) {
 x_104 = x_63;
} else {
 lean::inc(x_101);
 lean::dec(x_63);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_109);
x_111 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_110);
return x_112;
}
}
else
{
obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_40);
lean::dec(x_48);
x_115 = lean::cnstr_get(x_55, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_118 = x_55;
} else {
 lean::inc(x_115);
 lean::dec(x_55);
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
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_121);
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_122);
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_123);
return x_125;
}
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_40);
x_127 = lean::cnstr_get(x_47, 0);
x_129 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_130 = x_47;
} else {
 lean::inc(x_127);
 lean::dec(x_47);
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
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_132);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_133);
x_135 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_134);
return x_136;
}
}
else
{
obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_137 = lean::cnstr_get(x_39, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 x_140 = x_39;
} else {
 lean::inc(x_137);
 lean::dec(x_39);
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
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_142);
x_144 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_144, x_143);
return x_145;
}
}
}
lbl_13:
{
uint32 x_147; uint32 x_148; uint8 x_149; 
lean::dec(x_12);
x_147 = 116;
x_148 = lean::unbox_uint32(x_3);
x_149 = x_148 == x_147;
if (x_149 == 0)
{
uint32 x_151; uint8 x_152; 
lean::dec(x_9);
x_151 = 120;
x_152 = x_148 == x_151;
if (x_152 == 0)
{
obj* x_153; 
x_153 = lean::box(0);
x_10 = x_153;
goto lbl_11;
}
else
{
obj* x_155; 
lean::dec(x_0);
x_155 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_5);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_158; obj* x_160; obj* x_163; 
x_156 = lean::cnstr_get(x_155, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_155, 1);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_155, 2);
lean::inc(x_160);
lean::dec(x_155);
x_163 = l_lean_parser_parse__hex__digit___at_lean_ir_parse__literal___spec__7(x_158);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_174; uint32 x_177; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_164 = lean::cnstr_get(x_163, 0);
x_166 = lean::cnstr_get(x_163, 1);
x_168 = lean::cnstr_get(x_163, 2);
if (lean::is_exclusive(x_163)) {
 x_170 = x_163;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_163);
 x_170 = lean::box(0);
}
x_171 = lean::mk_nat_obj(16u);
x_172 = lean::nat_mul(x_171, x_156);
lean::dec(x_156);
x_174 = lean::nat_add(x_172, x_164);
lean::dec(x_164);
lean::dec(x_172);
x_177 = l_char_of__nat(x_174);
lean::dec(x_174);
x_179 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_180 = lean::box_uint32(x_177);
if (lean::is_scalar(x_170)) {
 x_181 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_181 = x_170;
}
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_166);
lean::cnstr_set(x_181, 2, x_179);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_168, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_160, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_183);
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_179, x_184);
return x_185;
}
else
{
obj* x_187; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_156);
x_187 = lean::cnstr_get(x_163, 0);
x_189 = lean::cnstr_get_scalar<uint8>(x_163, sizeof(void*)*1);
if (lean::is_exclusive(x_163)) {
 x_190 = x_163;
} else {
 lean::inc(x_187);
 lean::dec(x_163);
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
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_160, x_192);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_193);
x_195 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_194);
return x_196;
}
}
else
{
obj* x_197; uint8 x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
x_197 = lean::cnstr_get(x_155, 0);
x_199 = lean::cnstr_get_scalar<uint8>(x_155, sizeof(void*)*1);
if (lean::is_exclusive(x_155)) {
 x_200 = x_155;
} else {
 lean::inc(x_197);
 lean::dec(x_155);
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
x_203 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_202);
x_204 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_204, x_203);
return x_205;
}
}
}
else
{
uint32 x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_0);
x_207 = 9;
x_208 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_209 = lean::box_uint32(x_207);
if (lean::is_scalar(x_9)) {
 x_210 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_210 = x_9;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_5);
lean::cnstr_set(x_210, 2, x_208);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_208, x_211);
return x_212;
}
}
lbl_15:
{
uint32 x_214; uint32 x_215; uint8 x_216; 
lean::dec(x_14);
x_214 = 34;
x_215 = lean::unbox_uint32(x_3);
x_216 = x_215 == x_214;
if (x_216 == 0)
{
uint32 x_217; uint8 x_218; 
x_217 = 39;
x_218 = x_215 == x_217;
if (x_218 == 0)
{
uint32 x_219; uint8 x_220; 
x_219 = 110;
x_220 = x_215 == x_219;
if (x_220 == 0)
{
obj* x_221; 
x_221 = lean::box(0);
x_12 = x_221;
goto lbl_13;
}
else
{
uint32 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_9);
lean::dec(x_0);
x_224 = 10;
x_225 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_226 = lean::box_uint32(x_224);
x_227 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_227, 0, x_226);
lean::cnstr_set(x_227, 1, x_5);
lean::cnstr_set(x_227, 2, x_225);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_227);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_225, x_228);
return x_229;
}
}
else
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_9);
lean::dec(x_0);
x_232 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_233 = lean::box_uint32(x_217);
x_234 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_5);
lean::cnstr_set(x_234, 2, x_232);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_234);
x_236 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_232, x_235);
return x_236;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
lean::dec(x_9);
lean::dec(x_0);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_240 = lean::box_uint32(x_214);
x_241 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_241, 0, x_240);
lean::cnstr_set(x_241, 1, x_5);
lean::cnstr_set(x_241, 2, x_239);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_241);
x_243 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_242);
return x_243;
}
}
}
else
{
obj* x_245; uint8 x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_0);
x_245 = lean::cnstr_get(x_2, 0);
x_247 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_248 = x_2;
} else {
 lean::inc(x_245);
 lean::dec(x_2);
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
x_251 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_252 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_251, x_250);
return x_252;
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
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_31, x_33, x_32, x_32, x_0);
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
x_47 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__13(x_46, x_41);
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
x_58 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__literal___spec__15(x_0, x_56);
lean::dec(x_0);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_58);
return x_60;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
lean::dec(x_0);
lean::dec(x_1);
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
lean::dec(x_0);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_103; uint16 x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_99 = lean::cnstr_get(x_96, 1);
x_101 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean::uint16_of_nat(x_1);
lean::dec(x_1);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_107 = lean::box(x_104);
if (lean::is_scalar(x_103)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_103;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_99);
lean::cnstr_set(x_108, 2, x_106);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_106, x_110);
x_112 = l_lean_parser_parsec__t_try__mk__res___rarg(x_111);
x_113 = l_lean_ir_parse__uint16___closed__1;
x_114 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_112, x_113);
return x_114;
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_1);
x_116 = lean::cnstr_get(x_96, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_119 = x_96;
} else {
 lean::inc(x_116);
 lean::dec(x_96);
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
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_121);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_122);
x_125 = l_lean_parser_parsec__t_try__mk__res___rarg(x_124);
x_126 = l_lean_ir_parse__uint16___closed__1;
x_127 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_125, x_126);
return x_127;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
lean::dec(x_0);
if (lean::obj_tag(x_96) == 0)
{
obj* x_99; obj* x_101; obj* x_103; usize x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_99 = lean::cnstr_get(x_96, 1);
x_101 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_103 = x_96;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean::usize_of_nat(x_1);
lean::dec(x_1);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_107 = lean::box_size_t(x_104);
if (lean::is_scalar(x_103)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_103;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_99);
lean::cnstr_set(x_108, 2, x_106);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_106, x_110);
x_112 = l_lean_parser_parsec__t_try__mk__res___rarg(x_111);
x_113 = l_lean_ir_parse__usize___closed__1;
x_114 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_112, x_113);
return x_114;
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_1);
x_116 = lean::cnstr_get(x_96, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_119 = x_96;
} else {
 lean::inc(x_116);
 lean::dec(x_96);
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
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_121);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_122);
x_125 = l_lean_parser_parsec__t_try__mk__res___rarg(x_124);
x_126 = l_lean_ir_parse__usize___closed__1;
x_127 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_125, x_126);
return x_127;
}
}
}
}
}
obj* l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = lean::string_iterator_curr(x_0);
x_2 = l_lean_ir_keyword___closed__1;
x_3 = lean::box_uint32(x_1);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_2);
return x_5;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__rest(x_10);
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__rest(x_10);
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__rest(x_10);
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
obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_27 = l_char_quote__core(x_25);
x_28 = l_char_has__repr___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_31 = lean::string_append(x_29, x_28);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
x_34 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_31, x_33, x_32, x_32, x_0);
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
x_47 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__7(x_46, x_41);
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
x_58 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__9(x_0, x_56);
lean::dec(x_0);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_58);
return x_60;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__end__escape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_10);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_19;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__end__escape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_10);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_19;
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
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_lean_is__id__end__escape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_10);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_19;
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
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_44; 
x_33 = l_char_quote__core(x_25);
x_34 = l_char_has__repr___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_37 = lean::string_append(x_35, x_34);
x_38 = lean::box(0);
x_39 = l_mjoin___rarg___closed__1;
x_40 = l_lean_parser_monad__parsec_error___at_lean_ir_keyword___spec__1___rarg(x_37, x_39, x_38, x_38, x_0);
lean::dec(x_0);
lean::dec(x_37);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_40);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_47; obj* x_49; uint32 x_52; obj* x_53; obj* x_54; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 2);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::unbox_uint32(x_45);
x_53 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_identifier___spec__17(x_52, x_47);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_53);
return x_54;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_44, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (lean::is_exclusive(x_44)) {
 x_58 = x_44;
} else {
 lean::inc(x_55);
 lean::dec(x_44);
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
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; 
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
lean::dec(x_8);
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_12);
x_17 = lean::cnstr_get(x_15, 0);
x_19 = lean::cnstr_get(x_15, 1);
x_21 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 lean::cnstr_set(x_15, 2, lean::box(0));
 x_23 = x_15;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_15);
 x_23 = lean::box(0);
}
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_1, x_24);
lean::inc(x_0);
x_27 = lean_name_mk_string(x_0, x_17);
x_28 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_ir_identifier___spec__20(x_27, x_25, x_19);
lean::dec(x_25);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_28);
if (lean::obj_tag(x_30) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_23);
return x_30;
}
else
{
obj* x_34; uint8 x_36; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_30);
x_38 = lean::cnstr_get(x_34, 2);
lean::inc(x_38);
lean::dec(x_34);
x_41 = l_mjoin___rarg___closed__1;
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_42, 0, x_38);
lean::closure_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
if (lean::is_scalar(x_23)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_23;
}
lean::cnstr_set(x_44, 0, x_0);
lean::cnstr_set(x_44, 1, x_2);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_23);
lean::dec(x_34);
return x_30;
}
}
}
else
{
obj* x_49; uint8 x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_15, 0);
x_51 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_52 = x_15;
} else {
 lean::inc(x_49);
 lean::dec(x_15);
 x_52 = lean::box(0);
}
if (x_51 == 0)
{
obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_52);
x_54 = lean::cnstr_get(x_49, 2);
lean::inc(x_54);
lean::dec(x_49);
x_57 = l_mjoin___rarg___closed__1;
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_58, 0, x_54);
lean::closure_set(x_58, 1, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
if (lean::is_scalar(x_12)) {
 x_60 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_60 = x_12;
}
lean::cnstr_set(x_60, 0, x_0);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_59);
return x_60;
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
if (lean::is_scalar(x_52)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_52;
}
lean::cnstr_set(x_64, 0, x_49);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_51);
x_65 = x_64;
return x_65;
}
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; 
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
obj* x_82; obj* x_83; 
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_0);
lean::cnstr_set(x_83, 1, x_2);
lean::cnstr_set(x_83, 2, x_82);
return x_83;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* x_1; 
x_1 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
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
x_9 = l_lean_ir_is__reserved__name___main(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = l_lean_ir_keyword___closed__1;
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_10);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_12);
x_15 = l_lean_parser_parsec__t_try__mk__res___rarg(x_14);
x_16 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_17 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_15, x_16);
return x_17;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_8);
x_19 = l_lean_ir_identifier___closed__1;
x_20 = l_lean_parser_monad__parsec_unexpected__at___at_lean_ir_parse__literal___spec__6___rarg(x_19, x_0, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_22 = lean::cnstr_get(x_20, 1);
x_24 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_26 = x_20;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_20);
 x_26 = lean::box(0);
}
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_2);
lean::cnstr_set(x_28, 1, x_22);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_28);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_30);
x_32 = l_lean_parser_parsec__t_try__mk__res___rarg(x_31);
x_33 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_34 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_32, x_33);
return x_34;
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_2);
x_36 = lean::cnstr_get(x_20, 0);
x_38 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_39 = x_20;
} else {
 lean::inc(x_36);
 lean::dec(x_20);
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
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_41);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_42);
x_45 = l_lean_parser_parsec__t_try__mk__res___rarg(x_44);
x_46 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_47 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_45, x_46);
return x_47;
}
}
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_48 = lean::cnstr_get(x_1, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_51 = x_1;
} else {
 lean::inc(x_48);
 lean::dec(x_1);
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
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_53);
x_56 = l_lean_parser_parsec__t_try__mk__res___rarg(x_55);
x_57 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1___closed__1;
x_58 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_56, x_57);
return x_58;
}
}
}
obj* l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_curr___at_lean_ir_identifier___spec__3(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_parser_id__part___at_lean_ir_identifier___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_id__part___at_lean_ir_identifier___spec__2(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_parser_identifier___at_lean_ir_identifier___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_identifier___at_lean_ir_identifier___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_identifier___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_identifier(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__var___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("variable");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* l_lean_ir_parse__var___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__var(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__fnid___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("function name");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* l_lean_ir_parse__fnid___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__fnid(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_parse__blockid___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("label");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
obj* l_lean_ir_parse__blockid___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__blockid(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__1(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_0);
x_8 = lean::alloc_cnstr(3, 3, 2);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*3, x_1);
x_9 = x_8;
lean::cnstr_set_scalar(x_9, sizeof(void*)*3 + 1, x_2);
x_10 = x_9;
return x_10;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__2(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(2, 2, 2);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_1);
x_7 = x_6;
lean::cnstr_set_scalar(x_7, sizeof(void*)*2 + 1, x_2);
x_8 = x_7;
return x_8;
}
}
obj* l_lean_ir_parse__typed__assignment___lambda__3(obj* x_0, uint8 x_1, obj* x_2, usize x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_2);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(10, 2, sizeof(size_t)*1 + 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set_scalar(x_6, sizeof(void*)*3, x_1);
x_7 = x_6;
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_3);
x_8 = x_7;
return x_8;
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
lean::dec(x_35);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_42 = lean::cnstr_get(x_40, 0);
x_44 = lean::cnstr_get(x_40, 1);
x_46 = lean::cnstr_get(x_40, 2);
if (lean::is_exclusive(x_40)) {
 x_48 = x_40;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_40);
 x_48 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__3___boxed), 4, 3);
lean::closure_set(x_51, 0, x_0);
lean::closure_set(x_51, 1, x_12);
lean::closure_set(x_51, 2, x_42);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_48)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_48;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_44);
lean::cnstr_set(x_53, 2, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_60; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_55, 2);
lean::inc(x_60);
lean::dec(x_55);
x_28 = x_56;
x_29 = x_58;
x_30 = x_60;
goto lbl_31;
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_55, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_66 = x_55;
} else {
 lean::inc(x_63);
 lean::dec(x_55);
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
x_26 = x_68;
goto lbl_27;
}
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
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
obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_98);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_99);
return x_100;
}
else
{
obj* x_101; uint8 x_103; obj* x_104; obj* x_105; uint8 x_106; 
x_101 = lean::cnstr_get(x_26, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_103 == 0)
{
obj* x_109; 
lean::dec(x_26);
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
x_126 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_123);
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
x_104 = x_123;
x_105 = x_130;
x_106 = x_132;
goto lbl_107;
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
x_104 = x_139;
x_105 = x_133;
x_106 = x_135;
goto lbl_107;
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_101);
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_145);
return x_146;
}
lbl_107:
{
obj* x_147; obj* x_148; uint8 x_149; 
if (x_106 == 0)
{
obj* x_152; obj* x_153; obj* x_155; 
lean::dec(x_104);
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
lean::dec(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_178; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_178 = lean::cnstr_get(x_176, 0);
x_180 = lean::cnstr_get(x_176, 1);
x_182 = lean::cnstr_get(x_176, 2);
if (lean::is_exclusive(x_176)) {
 x_184 = x_176;
} else {
 lean::inc(x_178);
 lean::inc(x_180);
 lean::inc(x_182);
 lean::dec(x_176);
 x_184 = lean::box(0);
}
x_185 = lean::apply_1(x_169, x_178);
if (lean::is_scalar(x_184)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_184;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_180);
lean::cnstr_set(x_186, 2, x_166);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_186);
x_188 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_192 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_188);
x_193 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_192);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_193);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_195);
return x_196;
}
else
{
obj* x_197; uint8 x_199; 
x_197 = lean::cnstr_get(x_188, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*1);
x_147 = x_188;
x_148 = x_197;
x_149 = x_199;
goto lbl_150;
}
}
else
{
obj* x_201; uint8 x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
lean::dec(x_169);
x_201 = lean::cnstr_get(x_176, 0);
x_203 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
 x_204 = x_176;
} else {
 lean::inc(x_201);
 lean::dec(x_176);
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
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_206);
if (lean::obj_tag(x_207) == 0)
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_211 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_207);
x_212 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_212);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_213);
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_214);
return x_215;
}
else
{
obj* x_216; uint8 x_218; 
x_216 = lean::cnstr_get(x_207, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get_scalar<uint8>(x_207, sizeof(void*)*1);
x_147 = x_207;
x_148 = x_216;
x_149 = x_218;
goto lbl_150;
}
}
}
else
{
obj* x_219; uint8 x_221; obj* x_222; obj* x_224; obj* x_225; 
x_219 = lean::cnstr_get(x_168, 0);
x_221 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_exclusive(x_168)) {
 x_222 = x_168;
} else {
 lean::inc(x_219);
 lean::dec(x_168);
 x_222 = lean::box(0);
}
lean::inc(x_219);
if (lean::is_scalar(x_222)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_222;
}
lean::cnstr_set(x_224, 0, x_219);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_221);
x_225 = x_224;
x_147 = x_225;
x_148 = x_219;
x_149 = x_221;
goto lbl_150;
}
}
else
{
obj* x_226; uint8 x_228; obj* x_229; obj* x_231; obj* x_232; 
x_226 = lean::cnstr_get(x_155, 0);
x_228 = lean::cnstr_get_scalar<uint8>(x_155, sizeof(void*)*1);
if (lean::is_exclusive(x_155)) {
 x_229 = x_155;
} else {
 lean::inc(x_226);
 lean::dec(x_155);
 x_229 = lean::box(0);
}
lean::inc(x_226);
if (lean::is_scalar(x_229)) {
 x_231 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_231 = x_229;
}
lean::cnstr_set(x_231, 0, x_226);
lean::cnstr_set_scalar(x_231, sizeof(void*)*1, x_228);
x_232 = x_231;
x_147 = x_232;
x_148 = x_226;
x_149 = x_228;
goto lbl_150;
}
}
else
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_0);
lean::dec(x_105);
lean::dec(x_12);
lean::dec(x_21);
x_237 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_104);
x_238 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_237);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_238);
x_240 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_239);
return x_240;
}
lbl_150:
{
obj* x_241; obj* x_242; uint8 x_243; obj* x_245; obj* x_246; obj* x_247; 
if (x_149 == 0)
{
obj* x_250; obj* x_251; obj* x_253; 
lean::dec(x_147);
x_250 = l_lean_ir_parse__typed__assignment___closed__4;
x_251 = l_lean_ir_str2abinop;
lean::inc(x_21);
x_253 = l_lean_ir_parse__key2val___main___rarg(x_250, x_251, x_21);
if (lean::obj_tag(x_253) == 0)
{
obj* x_254; obj* x_256; obj* x_258; obj* x_260; obj* x_263; obj* x_264; obj* x_265; obj* x_266; 
x_254 = lean::cnstr_get(x_253, 0);
x_256 = lean::cnstr_get(x_253, 1);
x_258 = lean::cnstr_get(x_253, 2);
if (lean::is_exclusive(x_253)) {
 x_260 = x_253;
} else {
 lean::inc(x_254);
 lean::inc(x_256);
 lean::inc(x_258);
 lean::dec(x_253);
 x_260 = lean::box(0);
}
lean::inc(x_12);
lean::inc(x_0);
x_263 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__typed__assignment___lambda__1___boxed), 5, 3);
lean::closure_set(x_263, 0, x_0);
lean::closure_set(x_263, 1, x_12);
lean::closure_set(x_263, 2, x_254);
x_264 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_260)) {
 x_265 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_265 = x_260;
}
lean::cnstr_set(x_265, 0, x_263);
lean::cnstr_set(x_265, 1, x_256);
lean::cnstr_set(x_265, 2, x_264);
x_266 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_265);
if (lean::obj_tag(x_266) == 0)
{
obj* x_267; obj* x_269; obj* x_271; obj* x_274; 
x_267 = lean::cnstr_get(x_266, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 1);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_266, 2);
lean::inc(x_271);
lean::dec(x_266);
x_274 = l_lean_ir_parse__var(x_269);
lean::dec(x_269);
if (lean::obj_tag(x_274) == 0)
{
obj* x_276; obj* x_278; obj* x_280; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_276 = lean::cnstr_get(x_274, 0);
x_278 = lean::cnstr_get(x_274, 1);
x_280 = lean::cnstr_get(x_274, 2);
if (lean::is_exclusive(x_274)) {
 x_282 = x_274;
} else {
 lean::inc(x_276);
 lean::inc(x_278);
 lean::inc(x_280);
 lean::dec(x_274);
 x_282 = lean::box(0);
}
x_283 = lean::apply_1(x_267, x_276);
if (lean::is_scalar(x_282)) {
 x_284 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_284 = x_282;
}
lean::cnstr_set(x_284, 0, x_283);
lean::cnstr_set(x_284, 1, x_278);
lean::cnstr_set(x_284, 2, x_264);
x_285 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_280, x_284);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_271, x_285);
if (lean::obj_tag(x_286) == 0)
{
obj* x_287; obj* x_289; obj* x_291; 
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_286, 2);
lean::inc(x_291);
lean::dec(x_286);
x_245 = x_287;
x_246 = x_289;
x_247 = x_291;
goto lbl_248;
}
else
{
obj* x_294; uint8 x_296; obj* x_297; obj* x_299; obj* x_300; 
x_294 = lean::cnstr_get(x_286, 0);
x_296 = lean::cnstr_get_scalar<uint8>(x_286, sizeof(void*)*1);
if (lean::is_exclusive(x_286)) {
 x_297 = x_286;
} else {
 lean::inc(x_294);
 lean::dec(x_286);
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
x_241 = x_300;
x_242 = x_294;
x_243 = x_296;
goto lbl_244;
}
}
else
{
obj* x_302; uint8 x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; 
lean::dec(x_267);
x_302 = lean::cnstr_get(x_274, 0);
x_304 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_exclusive(x_274)) {
 x_305 = x_274;
} else {
 lean::inc(x_302);
 lean::dec(x_274);
 x_305 = lean::box(0);
}
if (lean::is_scalar(x_305)) {
 x_306 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_306 = x_305;
}
lean::cnstr_set(x_306, 0, x_302);
lean::cnstr_set_scalar(x_306, sizeof(void*)*1, x_304);
x_307 = x_306;
x_308 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_271, x_307);
if (lean::obj_tag(x_308) == 0)
{
obj* x_309; obj* x_311; obj* x_313; 
x_309 = lean::cnstr_get(x_308, 0);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_308, 1);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_308, 2);
lean::inc(x_313);
lean::dec(x_308);
x_245 = x_309;
x_246 = x_311;
x_247 = x_313;
goto lbl_248;
}
else
{
obj* x_316; uint8 x_318; obj* x_319; obj* x_321; obj* x_322; 
x_316 = lean::cnstr_get(x_308, 0);
x_318 = lean::cnstr_get_scalar<uint8>(x_308, sizeof(void*)*1);
if (lean::is_exclusive(x_308)) {
 x_319 = x_308;
} else {
 lean::inc(x_316);
 lean::dec(x_308);
 x_319 = lean::box(0);
}
lean::inc(x_316);
if (lean::is_scalar(x_319)) {
 x_321 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_321 = x_319;
}
lean::cnstr_set(x_321, 0, x_316);
lean::cnstr_set_scalar(x_321, sizeof(void*)*1, x_318);
x_322 = x_321;
x_241 = x_322;
x_242 = x_316;
x_243 = x_318;
goto lbl_244;
}
}
}
else
{
obj* x_323; uint8 x_325; obj* x_326; obj* x_328; obj* x_329; 
x_323 = lean::cnstr_get(x_266, 0);
x_325 = lean::cnstr_get_scalar<uint8>(x_266, sizeof(void*)*1);
if (lean::is_exclusive(x_266)) {
 x_326 = x_266;
} else {
 lean::inc(x_323);
 lean::dec(x_266);
 x_326 = lean::box(0);
}
lean::inc(x_323);
if (lean::is_scalar(x_326)) {
 x_328 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_328 = x_326;
}
lean::cnstr_set(x_328, 0, x_323);
lean::cnstr_set_scalar(x_328, sizeof(void*)*1, x_325);
x_329 = x_328;
x_241 = x_329;
x_242 = x_323;
x_243 = x_325;
goto lbl_244;
}
}
else
{
obj* x_330; uint8 x_332; obj* x_333; obj* x_335; obj* x_336; 
x_330 = lean::cnstr_get(x_253, 0);
x_332 = lean::cnstr_get_scalar<uint8>(x_253, sizeof(void*)*1);
if (lean::is_exclusive(x_253)) {
 x_333 = x_253;
} else {
 lean::inc(x_330);
 lean::dec(x_253);
 x_333 = lean::box(0);
}
lean::inc(x_330);
if (lean::is_scalar(x_333)) {
 x_335 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_335 = x_333;
}
lean::cnstr_set(x_335, 0, x_330);
lean::cnstr_set_scalar(x_335, sizeof(void*)*1, x_332);
x_336 = x_335;
x_241 = x_336;
x_242 = x_330;
x_243 = x_332;
goto lbl_244;
}
}
else
{
obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
lean::dec(x_148);
x_341 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_147);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_342);
x_344 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_343);
x_345 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_344);
return x_345;
}
lbl_244:
{
if (x_243 == 0)
{
obj* x_347; 
lean::dec(x_241);
x_347 = l_lean_ir_parse__literal(x_21);
if (lean::obj_tag(x_347) == 0)
{
obj* x_348; obj* x_350; obj* x_352; obj* x_354; obj* x_355; uint8 x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
x_348 = lean::cnstr_get(x_347, 0);
x_350 = lean::cnstr_get(x_347, 1);
x_352 = lean::cnstr_get(x_347, 2);
if (lean::is_exclusive(x_347)) {
 x_354 = x_347;
} else {
 lean::inc(x_348);
 lean::inc(x_350);
 lean::inc(x_352);
 lean::dec(x_347);
 x_354 = lean::box(0);
}
x_355 = lean::alloc_cnstr(1, 2, 1);
lean::cnstr_set(x_355, 0, x_0);
lean::cnstr_set(x_355, 1, x_348);
x_356 = lean::unbox(x_12);
lean::cnstr_set_scalar(x_355, sizeof(void*)*2, x_356);
x_357 = x_355;
x_358 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_354)) {
 x_359 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_359 = x_354;
}
lean::cnstr_set(x_359, 0, x_357);
lean::cnstr_set(x_359, 1, x_350);
lean::cnstr_set(x_359, 2, x_358);
x_360 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_352, x_359);
x_361 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_242, x_360);
x_362 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_361);
x_363 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_362);
x_364 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_363);
x_365 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_364);
x_366 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_365);
x_367 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_366);
return x_367;
}
else
{
obj* x_370; uint8 x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; 
lean::dec(x_0);
lean::dec(x_12);
x_370 = lean::cnstr_get(x_347, 0);
x_372 = lean::cnstr_get_scalar<uint8>(x_347, sizeof(void*)*1);
if (lean::is_exclusive(x_347)) {
 x_373 = x_347;
} else {
 lean::inc(x_370);
 lean::dec(x_347);
 x_373 = lean::box(0);
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_370);
lean::cnstr_set_scalar(x_374, sizeof(void*)*1, x_372);
x_375 = x_374;
x_376 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_242, x_375);
x_377 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_376);
x_378 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_377);
x_379 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_378);
x_380 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_379);
x_381 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_380);
x_382 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_381);
return x_382;
}
}
else
{
obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
lean::dec(x_0);
lean::dec(x_242);
lean::dec(x_12);
lean::dec(x_21);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_241);
x_388 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_387);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_388);
x_390 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_389);
x_391 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_390);
x_392 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_391);
return x_392;
}
}
lbl_248:
{
obj* x_393; 
x_393 = l_lean_ir_parse__var(x_246);
lean::dec(x_246);
if (lean::obj_tag(x_393) == 0)
{
obj* x_395; obj* x_397; obj* x_399; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; 
x_395 = lean::cnstr_get(x_393, 0);
x_397 = lean::cnstr_get(x_393, 1);
x_399 = lean::cnstr_get(x_393, 2);
if (lean::is_exclusive(x_393)) {
 x_401 = x_393;
} else {
 lean::inc(x_395);
 lean::inc(x_397);
 lean::inc(x_399);
 lean::dec(x_393);
 x_401 = lean::box(0);
}
x_402 = lean::apply_1(x_245, x_395);
x_403 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_401)) {
 x_404 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_404 = x_401;
}
lean::cnstr_set(x_404, 0, x_402);
lean::cnstr_set(x_404, 1, x_397);
lean::cnstr_set(x_404, 2, x_403);
x_405 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_399, x_404);
x_406 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_405);
if (lean::obj_tag(x_406) == 0)
{
obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_410 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_406);
x_411 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_410);
x_412 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_411);
x_413 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_412);
x_414 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_413);
x_415 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_414);
return x_415;
}
else
{
obj* x_416; uint8 x_418; 
x_416 = lean::cnstr_get(x_406, 0);
lean::inc(x_416);
x_418 = lean::cnstr_get_scalar<uint8>(x_406, sizeof(void*)*1);
x_241 = x_406;
x_242 = x_416;
x_243 = x_418;
goto lbl_244;
}
}
else
{
obj* x_420; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; 
lean::dec(x_245);
x_420 = lean::cnstr_get(x_393, 0);
x_422 = lean::cnstr_get_scalar<uint8>(x_393, sizeof(void*)*1);
if (lean::is_exclusive(x_393)) {
 x_423 = x_393;
} else {
 lean::inc(x_420);
 lean::dec(x_393);
 x_423 = lean::box(0);
}
if (lean::is_scalar(x_423)) {
 x_424 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_424 = x_423;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set_scalar(x_424, sizeof(void*)*1, x_422);
x_425 = x_424;
x_426 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_425);
if (lean::obj_tag(x_426) == 0)
{
obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; 
lean::dec(x_0);
lean::dec(x_12);
lean::dec(x_21);
x_430 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_148, x_426);
x_431 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_105, x_430);
x_432 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_101, x_431);
x_433 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_432);
x_434 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_433);
x_435 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_434);
return x_435;
}
else
{
obj* x_436; uint8 x_438; 
x_436 = lean::cnstr_get(x_426, 0);
lean::inc(x_436);
x_438 = lean::cnstr_get_scalar<uint8>(x_426, sizeof(void*)*1);
x_241 = x_426;
x_242 = x_436;
x_243 = x_438;
goto lbl_244;
}
}
}
}
}
}
}
lbl_31:
{
obj* x_439; 
x_439 = l_lean_ir_parse__usize(x_29);
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
x_447 = lean::apply_1(x_28, x_440);
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
x_451 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_450);
x_26 = x_451;
goto lbl_27;
}
else
{
obj* x_453; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; 
lean::dec(x_28);
x_453 = lean::cnstr_get(x_439, 0);
x_455 = lean::cnstr_get_scalar<uint8>(x_439, sizeof(void*)*1);
if (lean::is_exclusive(x_439)) {
 x_456 = x_439;
} else {
 lean::inc(x_453);
 lean::dec(x_439);
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
x_459 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_458);
x_26 = x_459;
goto lbl_27;
}
}
}
else
{
obj* x_462; uint8 x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
lean::dec(x_0);
lean::dec(x_12);
x_462 = lean::cnstr_get(x_20, 0);
x_464 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_465 = x_20;
} else {
 lean::inc(x_462);
 lean::dec(x_20);
 x_465 = lean::box(0);
}
if (lean::is_scalar(x_465)) {
 x_466 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_466 = x_465;
}
lean::cnstr_set(x_466, 0, x_462);
lean::cnstr_set_scalar(x_466, sizeof(void*)*1, x_464);
x_467 = x_466;
x_468 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_467);
x_469 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_468);
return x_469;
}
}
else
{
obj* x_471; uint8 x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
lean::dec(x_0);
x_471 = lean::cnstr_get(x_11, 0);
x_473 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_474 = x_11;
} else {
 lean::inc(x_471);
 lean::dec(x_11);
 x_474 = lean::box(0);
}
if (lean::is_scalar(x_474)) {
 x_475 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_475 = x_474;
}
lean::cnstr_set(x_475, 0, x_471);
lean::cnstr_set_scalar(x_475, sizeof(void*)*1, x_473);
x_476 = x_475;
x_477 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_476);
return x_477;
}
}
else
{
obj* x_479; uint8 x_481; obj* x_482; obj* x_483; obj* x_484; 
lean::dec(x_0);
x_479 = lean::cnstr_get(x_3, 0);
x_481 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_482 = x_3;
} else {
 lean::inc(x_479);
 lean::dec(x_3);
 x_482 = lean::box(0);
}
if (lean::is_scalar(x_482)) {
 x_483 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_483 = x_482;
}
lean::cnstr_set(x_483, 0, x_479);
lean::cnstr_set_scalar(x_483, sizeof(void*)*1, x_481);
x_484 = x_483;
return x_484;
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
lean::dec(x_0);
lean::dec(x_3);
lean::dec(x_4);
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
lean::dec(x_0);
lean::dec(x_3);
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
lean::dec(x_0);
lean::dec(x_2);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_mjoin___rarg___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_0);
lean::cnstr_set(x_14, 2, x_12);
return x_14;
}
else
{
lean::dec(x_2);
return x_1;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_mjoin___rarg___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_0);
lean::cnstr_set(x_14, 2, x_12);
return x_14;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_0);
x_7 = lean::alloc_cnstr(14, 3, 1);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_1);
x_8 = x_7;
return x_8;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(13, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
return x_6;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__3(obj* x_0, uint16 x_1, uint16 x_2, usize x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_5 = lean::alloc_cnstr(6, 1, sizeof(size_t)*1 + 4);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_1);
x_6 = x_5;
lean::cnstr_set_scalar(x_6, sizeof(void*)*2 + 2, x_2);
x_7 = x_6;
lean::cnstr_set_scalar(x_7, sizeof(void*)*1, x_3);
x_8 = x_7;
return x_8;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
return x_6;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__5(obj* x_0, obj* x_1, uint16 x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(8, 2, 2);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_2);
x_6 = x_5;
return x_6;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(11, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
return x_6;
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
lean::dec(x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_25 = lean::cnstr_get(x_23, 0);
x_27 = lean::cnstr_get(x_23, 1);
x_29 = lean::cnstr_get(x_23, 2);
if (lean::is_exclusive(x_23)) {
 x_31 = x_23;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
lean::inc(x_0);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__6___boxed), 3, 2);
lean::closure_set(x_33, 0, x_0);
lean::closure_set(x_33, 1, x_25);
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_27);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_42; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 2);
lean::inc(x_42);
lean::dec(x_37);
x_11 = x_38;
x_12 = x_40;
x_13 = x_42;
goto lbl_14;
}
else
{
obj* x_45; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_37, 0);
x_47 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_45);
 lean::dec(x_37);
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
x_9 = x_50;
goto lbl_10;
}
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
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
obj* x_79; 
lean::dec(x_4);
lean::dec(x_0);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; uint8 x_85; 
x_80 = lean::cnstr_get(x_9, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_88; obj* x_90; 
lean::dec(x_9);
x_88 = l_lean_ir_parse__untyped__assignment___closed__6;
lean::inc(x_4);
x_90 = l_lean_ir_keyword(x_88, x_4);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_93; obj* x_96; 
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 2);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(x_91);
lean::dec(x_91);
if (lean::obj_tag(x_96) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_98 = lean::cnstr_get(x_96, 0);
x_100 = lean::cnstr_get(x_96, 1);
x_102 = lean::cnstr_get(x_96, 2);
if (lean::is_exclusive(x_96)) {
 x_104 = x_96;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_96);
 x_104 = lean::box(0);
}
lean::inc(x_0);
x_106 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_106, 0, x_0);
lean::cnstr_set(x_106, 1, x_98);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_104)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_104;
}
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_100);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_113; obj* x_114; 
lean::dec(x_4);
lean::dec(x_0);
x_113 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_110);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_113);
return x_114;
}
else
{
obj* x_115; uint8 x_117; 
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
x_83 = x_110;
x_84 = x_115;
x_85 = x_117;
goto lbl_86;
}
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_118 = lean::cnstr_get(x_96, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_121 = x_96;
} else {
 lean::inc(x_118);
 lean::dec(x_96);
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
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_127; obj* x_128; 
lean::dec(x_4);
lean::dec(x_0);
x_127 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_124);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_127);
return x_128;
}
else
{
obj* x_129; uint8 x_131; 
x_129 = lean::cnstr_get(x_124, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*1);
x_83 = x_124;
x_84 = x_129;
x_85 = x_131;
goto lbl_86;
}
}
}
else
{
obj* x_132; uint8 x_134; obj* x_135; obj* x_137; obj* x_138; 
x_132 = lean::cnstr_get(x_90, 0);
x_134 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (lean::is_exclusive(x_90)) {
 x_135 = x_90;
} else {
 lean::inc(x_132);
 lean::dec(x_90);
 x_135 = lean::box(0);
}
lean::inc(x_132);
if (lean::is_scalar(x_135)) {
 x_137 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_137 = x_135;
}
lean::cnstr_set(x_137, 0, x_132);
lean::cnstr_set_scalar(x_137, sizeof(void*)*1, x_134);
x_138 = x_137;
x_83 = x_138;
x_84 = x_132;
x_85 = x_134;
goto lbl_86;
}
}
else
{
obj* x_142; 
lean::dec(x_80);
lean::dec(x_4);
lean::dec(x_0);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_9);
return x_142;
}
lbl_86:
{
obj* x_143; obj* x_144; uint8 x_145; obj* x_147; obj* x_148; obj* x_149; 
if (x_85 == 0)
{
obj* x_152; obj* x_154; 
lean::dec(x_83);
x_152 = l_lean_ir_parse__untyped__assignment___closed__5;
lean::inc(x_4);
x_154 = l_lean_ir_keyword(x_152, x_4);
if (lean::obj_tag(x_154) == 0)
{
obj* x_155; obj* x_157; obj* x_160; 
x_155 = lean::cnstr_get(x_154, 1);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_154, 2);
lean::inc(x_157);
lean::dec(x_154);
x_160 = l_lean_ir_parse__var(x_155);
lean::dec(x_155);
if (lean::obj_tag(x_160) == 0)
{
obj* x_162; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
x_162 = lean::cnstr_get(x_160, 0);
x_164 = lean::cnstr_get(x_160, 1);
x_166 = lean::cnstr_get(x_160, 2);
if (lean::is_exclusive(x_160)) {
 x_168 = x_160;
} else {
 lean::inc(x_162);
 lean::inc(x_164);
 lean::inc(x_166);
 lean::dec(x_160);
 x_168 = lean::box(0);
}
lean::inc(x_0);
x_170 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__5___boxed), 3, 2);
lean::closure_set(x_170, 0, x_0);
lean::closure_set(x_170, 1, x_162);
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
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_157, x_173);
if (lean::obj_tag(x_174) == 0)
{
obj* x_175; obj* x_177; obj* x_179; 
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 1);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_174, 2);
lean::inc(x_179);
lean::dec(x_174);
x_147 = x_175;
x_148 = x_177;
x_149 = x_179;
goto lbl_150;
}
else
{
obj* x_182; uint8 x_184; obj* x_185; obj* x_187; obj* x_188; 
x_182 = lean::cnstr_get(x_174, 0);
x_184 = lean::cnstr_get_scalar<uint8>(x_174, sizeof(void*)*1);
if (lean::is_exclusive(x_174)) {
 x_185 = x_174;
} else {
 lean::inc(x_182);
 lean::dec(x_174);
 x_185 = lean::box(0);
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
x_143 = x_188;
x_144 = x_182;
x_145 = x_184;
goto lbl_146;
}
}
else
{
obj* x_189; uint8 x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_189 = lean::cnstr_get(x_160, 0);
x_191 = lean::cnstr_get_scalar<uint8>(x_160, sizeof(void*)*1);
if (lean::is_exclusive(x_160)) {
 x_192 = x_160;
} else {
 lean::inc(x_189);
 lean::dec(x_160);
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
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_157, x_194);
if (lean::obj_tag(x_195) == 0)
{
obj* x_196; obj* x_198; obj* x_200; 
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_195, 2);
lean::inc(x_200);
lean::dec(x_195);
x_147 = x_196;
x_148 = x_198;
x_149 = x_200;
goto lbl_150;
}
else
{
obj* x_203; uint8 x_205; obj* x_206; obj* x_208; obj* x_209; 
x_203 = lean::cnstr_get(x_195, 0);
x_205 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_exclusive(x_195)) {
 x_206 = x_195;
} else {
 lean::inc(x_203);
 lean::dec(x_195);
 x_206 = lean::box(0);
}
lean::inc(x_203);
if (lean::is_scalar(x_206)) {
 x_208 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_208 = x_206;
}
lean::cnstr_set(x_208, 0, x_203);
lean::cnstr_set_scalar(x_208, sizeof(void*)*1, x_205);
x_209 = x_208;
x_143 = x_209;
x_144 = x_203;
x_145 = x_205;
goto lbl_146;
}
}
}
else
{
obj* x_210; uint8 x_212; obj* x_213; obj* x_215; obj* x_216; 
x_210 = lean::cnstr_get(x_154, 0);
x_212 = lean::cnstr_get_scalar<uint8>(x_154, sizeof(void*)*1);
if (lean::is_exclusive(x_154)) {
 x_213 = x_154;
} else {
 lean::inc(x_210);
 lean::dec(x_154);
 x_213 = lean::box(0);
}
lean::inc(x_210);
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_210);
lean::cnstr_set_scalar(x_215, sizeof(void*)*1, x_212);
x_216 = x_215;
x_143 = x_216;
x_144 = x_210;
x_145 = x_212;
goto lbl_146;
}
}
else
{
obj* x_220; obj* x_221; 
lean::dec(x_84);
lean::dec(x_4);
lean::dec(x_0);
x_220 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_83);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_220);
return x_221;
}
lbl_146:
{
obj* x_222; obj* x_223; uint8 x_224; obj* x_226; obj* x_227; obj* x_228; 
if (x_145 == 0)
{
obj* x_231; obj* x_233; 
lean::dec(x_143);
x_231 = l_lean_ir_parse__untyped__assignment___closed__4;
lean::inc(x_4);
x_233 = l_lean_ir_keyword(x_231, x_4);
if (lean::obj_tag(x_233) == 0)
{
obj* x_234; obj* x_236; obj* x_239; 
x_234 = lean::cnstr_get(x_233, 1);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_233, 2);
lean::inc(x_236);
lean::dec(x_233);
x_239 = l_lean_ir_parse__fnid(x_234);
lean::dec(x_234);
if (lean::obj_tag(x_239) == 0)
{
obj* x_241; obj* x_243; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
x_241 = lean::cnstr_get(x_239, 0);
x_243 = lean::cnstr_get(x_239, 1);
x_245 = lean::cnstr_get(x_239, 2);
if (lean::is_exclusive(x_239)) {
 x_247 = x_239;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::inc(x_245);
 lean::dec(x_239);
 x_247 = lean::box(0);
}
lean::inc(x_0);
x_249 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__4___boxed), 3, 2);
lean::closure_set(x_249, 0, x_0);
lean::closure_set(x_249, 1, x_241);
x_250 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_247)) {
 x_251 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_251 = x_247;
}
lean::cnstr_set(x_251, 0, x_249);
lean::cnstr_set(x_251, 1, x_243);
lean::cnstr_set(x_251, 2, x_250);
x_252 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_245, x_251);
x_253 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_236, x_252);
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
x_226 = x_254;
x_227 = x_256;
x_228 = x_258;
goto lbl_229;
}
else
{
obj* x_261; uint8 x_263; obj* x_264; obj* x_266; obj* x_267; 
x_261 = lean::cnstr_get(x_253, 0);
x_263 = lean::cnstr_get_scalar<uint8>(x_253, sizeof(void*)*1);
if (lean::is_exclusive(x_253)) {
 x_264 = x_253;
} else {
 lean::inc(x_261);
 lean::dec(x_253);
 x_264 = lean::box(0);
}
lean::inc(x_261);
if (lean::is_scalar(x_264)) {
 x_266 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_266 = x_264;
}
lean::cnstr_set(x_266, 0, x_261);
lean::cnstr_set_scalar(x_266, sizeof(void*)*1, x_263);
x_267 = x_266;
x_222 = x_267;
x_223 = x_261;
x_224 = x_263;
goto lbl_225;
}
}
else
{
obj* x_268; uint8 x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_268 = lean::cnstr_get(x_239, 0);
x_270 = lean::cnstr_get_scalar<uint8>(x_239, sizeof(void*)*1);
if (lean::is_exclusive(x_239)) {
 x_271 = x_239;
} else {
 lean::inc(x_268);
 lean::dec(x_239);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_268);
lean::cnstr_set_scalar(x_272, sizeof(void*)*1, x_270);
x_273 = x_272;
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_236, x_273);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_277; obj* x_279; 
x_275 = lean::cnstr_get(x_274, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 1);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_274, 2);
lean::inc(x_279);
lean::dec(x_274);
x_226 = x_275;
x_227 = x_277;
x_228 = x_279;
goto lbl_229;
}
else
{
obj* x_282; uint8 x_284; obj* x_285; obj* x_287; obj* x_288; 
x_282 = lean::cnstr_get(x_274, 0);
x_284 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_exclusive(x_274)) {
 x_285 = x_274;
} else {
 lean::inc(x_282);
 lean::dec(x_274);
 x_285 = lean::box(0);
}
lean::inc(x_282);
if (lean::is_scalar(x_285)) {
 x_287 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_287 = x_285;
}
lean::cnstr_set(x_287, 0, x_282);
lean::cnstr_set_scalar(x_287, sizeof(void*)*1, x_284);
x_288 = x_287;
x_222 = x_288;
x_223 = x_282;
x_224 = x_284;
goto lbl_225;
}
}
}
else
{
obj* x_289; uint8 x_291; obj* x_292; obj* x_294; obj* x_295; 
x_289 = lean::cnstr_get(x_233, 0);
x_291 = lean::cnstr_get_scalar<uint8>(x_233, sizeof(void*)*1);
if (lean::is_exclusive(x_233)) {
 x_292 = x_233;
} else {
 lean::inc(x_289);
 lean::dec(x_233);
 x_292 = lean::box(0);
}
lean::inc(x_289);
if (lean::is_scalar(x_292)) {
 x_294 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_294 = x_292;
}
lean::cnstr_set(x_294, 0, x_289);
lean::cnstr_set_scalar(x_294, sizeof(void*)*1, x_291);
x_295 = x_294;
x_222 = x_295;
x_223 = x_289;
x_224 = x_291;
goto lbl_225;
}
}
else
{
obj* x_299; obj* x_300; obj* x_301; 
lean::dec(x_144);
lean::dec(x_4);
lean::dec(x_0);
x_299 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_143);
x_300 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_299);
x_301 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_300);
return x_301;
}
lbl_225:
{
obj* x_302; obj* x_303; uint8 x_304; obj* x_306; obj* x_307; obj* x_308; obj* x_310; obj* x_311; obj* x_312; 
if (x_224 == 0)
{
obj* x_315; obj* x_317; 
lean::dec(x_222);
x_315 = l_lean_ir_parse__untyped__assignment___closed__3;
lean::inc(x_4);
x_317 = l_lean_ir_keyword(x_315, x_4);
if (lean::obj_tag(x_317) == 0)
{
obj* x_318; obj* x_320; obj* x_323; 
x_318 = lean::cnstr_get(x_317, 1);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_317, 2);
lean::inc(x_320);
lean::dec(x_317);
x_323 = l_lean_ir_parse__uint16(x_318);
if (lean::obj_tag(x_323) == 0)
{
obj* x_324; obj* x_326; obj* x_328; obj* x_330; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_324 = lean::cnstr_get(x_323, 0);
x_326 = lean::cnstr_get(x_323, 1);
x_328 = lean::cnstr_get(x_323, 2);
if (lean::is_exclusive(x_323)) {
 x_330 = x_323;
} else {
 lean::inc(x_324);
 lean::inc(x_326);
 lean::inc(x_328);
 lean::dec(x_323);
 x_330 = lean::box(0);
}
lean::inc(x_0);
x_332 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__3___boxed), 4, 2);
lean::closure_set(x_332, 0, x_0);
lean::closure_set(x_332, 1, x_324);
x_333 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_330)) {
 x_334 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_334 = x_330;
}
lean::cnstr_set(x_334, 0, x_332);
lean::cnstr_set(x_334, 1, x_326);
lean::cnstr_set(x_334, 2, x_333);
x_335 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_328, x_334);
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_320, x_335);
if (lean::obj_tag(x_336) == 0)
{
obj* x_337; obj* x_339; obj* x_341; 
x_337 = lean::cnstr_get(x_336, 0);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_336, 1);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_336, 2);
lean::inc(x_341);
lean::dec(x_336);
x_310 = x_337;
x_311 = x_339;
x_312 = x_341;
goto lbl_313;
}
else
{
obj* x_344; uint8 x_346; obj* x_347; obj* x_349; obj* x_350; 
x_344 = lean::cnstr_get(x_336, 0);
x_346 = lean::cnstr_get_scalar<uint8>(x_336, sizeof(void*)*1);
if (lean::is_exclusive(x_336)) {
 x_347 = x_336;
} else {
 lean::inc(x_344);
 lean::dec(x_336);
 x_347 = lean::box(0);
}
lean::inc(x_344);
if (lean::is_scalar(x_347)) {
 x_349 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_349 = x_347;
}
lean::cnstr_set(x_349, 0, x_344);
lean::cnstr_set_scalar(x_349, sizeof(void*)*1, x_346);
x_350 = x_349;
x_302 = x_350;
x_303 = x_344;
x_304 = x_346;
goto lbl_305;
}
}
else
{
obj* x_351; uint8 x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; 
x_351 = lean::cnstr_get(x_323, 0);
x_353 = lean::cnstr_get_scalar<uint8>(x_323, sizeof(void*)*1);
if (lean::is_exclusive(x_323)) {
 x_354 = x_323;
} else {
 lean::inc(x_351);
 lean::dec(x_323);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_351);
lean::cnstr_set_scalar(x_355, sizeof(void*)*1, x_353);
x_356 = x_355;
x_357 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_320, x_356);
if (lean::obj_tag(x_357) == 0)
{
obj* x_358; obj* x_360; obj* x_362; 
x_358 = lean::cnstr_get(x_357, 0);
lean::inc(x_358);
x_360 = lean::cnstr_get(x_357, 1);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_357, 2);
lean::inc(x_362);
lean::dec(x_357);
x_310 = x_358;
x_311 = x_360;
x_312 = x_362;
goto lbl_313;
}
else
{
obj* x_365; uint8 x_367; obj* x_368; obj* x_370; obj* x_371; 
x_365 = lean::cnstr_get(x_357, 0);
x_367 = lean::cnstr_get_scalar<uint8>(x_357, sizeof(void*)*1);
if (lean::is_exclusive(x_357)) {
 x_368 = x_357;
} else {
 lean::inc(x_365);
 lean::dec(x_357);
 x_368 = lean::box(0);
}
lean::inc(x_365);
if (lean::is_scalar(x_368)) {
 x_370 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_370 = x_368;
}
lean::cnstr_set(x_370, 0, x_365);
lean::cnstr_set_scalar(x_370, sizeof(void*)*1, x_367);
x_371 = x_370;
x_302 = x_371;
x_303 = x_365;
x_304 = x_367;
goto lbl_305;
}
}
}
else
{
obj* x_372; uint8 x_374; obj* x_375; obj* x_377; obj* x_378; 
x_372 = lean::cnstr_get(x_317, 0);
x_374 = lean::cnstr_get_scalar<uint8>(x_317, sizeof(void*)*1);
if (lean::is_exclusive(x_317)) {
 x_375 = x_317;
} else {
 lean::inc(x_372);
 lean::dec(x_317);
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
x_302 = x_378;
x_303 = x_372;
x_304 = x_374;
goto lbl_305;
}
}
else
{
obj* x_382; obj* x_383; obj* x_384; obj* x_385; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_223);
x_382 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_222);
x_383 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_382);
x_384 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_383);
x_385 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_384);
return x_385;
}
lbl_305:
{
obj* x_386; obj* x_387; uint8 x_388; obj* x_390; obj* x_391; obj* x_392; 
if (x_304 == 0)
{
obj* x_395; obj* x_397; 
lean::dec(x_302);
x_395 = l_lean_ir_parse__untyped__assignment___closed__2;
lean::inc(x_4);
x_397 = l_lean_ir_keyword(x_395, x_4);
if (lean::obj_tag(x_397) == 0)
{
obj* x_398; obj* x_400; obj* x_403; 
x_398 = lean::cnstr_get(x_397, 1);
lean::inc(x_398);
x_400 = lean::cnstr_get(x_397, 2);
lean::inc(x_400);
lean::dec(x_397);
x_403 = l_lean_ir_parse__var(x_398);
lean::dec(x_398);
if (lean::obj_tag(x_403) == 0)
{
obj* x_405; obj* x_407; obj* x_409; obj* x_411; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; 
x_405 = lean::cnstr_get(x_403, 0);
x_407 = lean::cnstr_get(x_403, 1);
x_409 = lean::cnstr_get(x_403, 2);
if (lean::is_exclusive(x_403)) {
 x_411 = x_403;
} else {
 lean::inc(x_405);
 lean::inc(x_407);
 lean::inc(x_409);
 lean::dec(x_403);
 x_411 = lean::box(0);
}
lean::inc(x_0);
x_413 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__2___boxed), 3, 2);
lean::closure_set(x_413, 0, x_0);
lean::closure_set(x_413, 1, x_405);
x_414 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_411)) {
 x_415 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_415 = x_411;
}
lean::cnstr_set(x_415, 0, x_413);
lean::cnstr_set(x_415, 1, x_407);
lean::cnstr_set(x_415, 2, x_414);
x_416 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_409, x_415);
x_417 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_400, x_416);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; obj* x_420; obj* x_422; 
x_418 = lean::cnstr_get(x_417, 0);
lean::inc(x_418);
x_420 = lean::cnstr_get(x_417, 1);
lean::inc(x_420);
x_422 = lean::cnstr_get(x_417, 2);
lean::inc(x_422);
lean::dec(x_417);
x_390 = x_418;
x_391 = x_420;
x_392 = x_422;
goto lbl_393;
}
else
{
obj* x_425; uint8 x_427; obj* x_428; obj* x_430; obj* x_431; 
x_425 = lean::cnstr_get(x_417, 0);
x_427 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*1);
if (lean::is_exclusive(x_417)) {
 x_428 = x_417;
} else {
 lean::inc(x_425);
 lean::dec(x_417);
 x_428 = lean::box(0);
}
lean::inc(x_425);
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_425);
lean::cnstr_set_scalar(x_430, sizeof(void*)*1, x_427);
x_431 = x_430;
x_386 = x_431;
x_387 = x_425;
x_388 = x_427;
goto lbl_389;
}
}
else
{
obj* x_432; uint8 x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; 
x_432 = lean::cnstr_get(x_403, 0);
x_434 = lean::cnstr_get_scalar<uint8>(x_403, sizeof(void*)*1);
if (lean::is_exclusive(x_403)) {
 x_435 = x_403;
} else {
 lean::inc(x_432);
 lean::dec(x_403);
 x_435 = lean::box(0);
}
if (lean::is_scalar(x_435)) {
 x_436 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_436 = x_435;
}
lean::cnstr_set(x_436, 0, x_432);
lean::cnstr_set_scalar(x_436, sizeof(void*)*1, x_434);
x_437 = x_436;
x_438 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_400, x_437);
if (lean::obj_tag(x_438) == 0)
{
obj* x_439; obj* x_441; obj* x_443; 
x_439 = lean::cnstr_get(x_438, 0);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_438, 1);
lean::inc(x_441);
x_443 = lean::cnstr_get(x_438, 2);
lean::inc(x_443);
lean::dec(x_438);
x_390 = x_439;
x_391 = x_441;
x_392 = x_443;
goto lbl_393;
}
else
{
obj* x_446; uint8 x_448; obj* x_449; obj* x_451; obj* x_452; 
x_446 = lean::cnstr_get(x_438, 0);
x_448 = lean::cnstr_get_scalar<uint8>(x_438, sizeof(void*)*1);
if (lean::is_exclusive(x_438)) {
 x_449 = x_438;
} else {
 lean::inc(x_446);
 lean::dec(x_438);
 x_449 = lean::box(0);
}
lean::inc(x_446);
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*1, x_448);
x_452 = x_451;
x_386 = x_452;
x_387 = x_446;
x_388 = x_448;
goto lbl_389;
}
}
}
else
{
obj* x_453; uint8 x_455; obj* x_456; obj* x_458; obj* x_459; 
x_453 = lean::cnstr_get(x_397, 0);
x_455 = lean::cnstr_get_scalar<uint8>(x_397, sizeof(void*)*1);
if (lean::is_exclusive(x_397)) {
 x_456 = x_397;
} else {
 lean::inc(x_453);
 lean::dec(x_397);
 x_456 = lean::box(0);
}
lean::inc(x_453);
if (lean::is_scalar(x_456)) {
 x_458 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_458 = x_456;
}
lean::cnstr_set(x_458, 0, x_453);
lean::cnstr_set_scalar(x_458, sizeof(void*)*1, x_455);
x_459 = x_458;
x_386 = x_459;
x_387 = x_453;
x_388 = x_455;
goto lbl_389;
}
}
else
{
obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_303);
x_463 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_302);
x_464 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_463);
x_465 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_464);
x_466 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_465);
x_467 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_466);
return x_467;
}
lbl_389:
{
obj* x_468; obj* x_469; obj* x_470; obj* x_472; obj* x_473; obj* x_474; 
if (x_388 == 0)
{
obj* x_477; obj* x_478; 
lean::dec(x_386);
x_477 = l_lean_ir_parse__untyped__assignment___closed__1;
x_478 = l_lean_ir_keyword(x_477, x_4);
if (lean::obj_tag(x_478) == 0)
{
obj* x_479; obj* x_481; obj* x_484; obj* x_485; obj* x_486; 
x_479 = lean::cnstr_get(x_478, 1);
lean::inc(x_479);
x_481 = lean::cnstr_get(x_478, 2);
lean::inc(x_481);
lean::dec(x_478);
x_484 = l_lean_ir_parse__typed__assignment___closed__2;
x_485 = l_lean_ir_str2type;
x_486 = l_lean_ir_parse__key2val___main___rarg(x_484, x_485, x_479);
if (lean::obj_tag(x_486) == 0)
{
obj* x_487; obj* x_489; obj* x_491; obj* x_493; obj* x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_498; 
x_487 = lean::cnstr_get(x_486, 0);
x_489 = lean::cnstr_get(x_486, 1);
x_491 = lean::cnstr_get(x_486, 2);
if (lean::is_exclusive(x_486)) {
 x_493 = x_486;
} else {
 lean::inc(x_487);
 lean::inc(x_489);
 lean::inc(x_491);
 lean::dec(x_486);
 x_493 = lean::box(0);
}
x_494 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__untyped__assignment___lambda__1___boxed), 4, 2);
lean::closure_set(x_494, 0, x_0);
lean::closure_set(x_494, 1, x_487);
x_495 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_493)) {
 x_496 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_496 = x_493;
}
lean::cnstr_set(x_496, 0, x_494);
lean::cnstr_set(x_496, 1, x_489);
lean::cnstr_set(x_496, 2, x_495);
x_497 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_491, x_496);
x_498 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_481, x_497);
if (lean::obj_tag(x_498) == 0)
{
obj* x_499; obj* x_501; obj* x_503; 
x_499 = lean::cnstr_get(x_498, 0);
lean::inc(x_499);
x_501 = lean::cnstr_get(x_498, 1);
lean::inc(x_501);
x_503 = lean::cnstr_get(x_498, 2);
lean::inc(x_503);
lean::dec(x_498);
x_472 = x_499;
x_473 = x_501;
x_474 = x_503;
goto lbl_475;
}
else
{
obj* x_506; uint8 x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; 
x_506 = lean::cnstr_get(x_498, 0);
x_508 = lean::cnstr_get_scalar<uint8>(x_498, sizeof(void*)*1);
if (lean::is_exclusive(x_498)) {
 x_509 = x_498;
} else {
 lean::inc(x_506);
 lean::dec(x_498);
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
x_512 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_511);
x_513 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_512);
x_514 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_513);
x_515 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_514);
x_516 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_515);
x_517 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_516);
x_518 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_517);
return x_518;
}
}
else
{
obj* x_520; uint8 x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; 
lean::dec(x_0);
x_520 = lean::cnstr_get(x_486, 0);
x_522 = lean::cnstr_get_scalar<uint8>(x_486, sizeof(void*)*1);
if (lean::is_exclusive(x_486)) {
 x_523 = x_486;
} else {
 lean::inc(x_520);
 lean::dec(x_486);
 x_523 = lean::box(0);
}
if (lean::is_scalar(x_523)) {
 x_524 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_524 = x_523;
}
lean::cnstr_set(x_524, 0, x_520);
lean::cnstr_set_scalar(x_524, sizeof(void*)*1, x_522);
x_525 = x_524;
x_526 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_481, x_525);
if (lean::obj_tag(x_526) == 0)
{
obj* x_527; obj* x_529; obj* x_531; 
x_527 = lean::cnstr_get(x_526, 0);
lean::inc(x_527);
x_529 = lean::cnstr_get(x_526, 1);
lean::inc(x_529);
x_531 = lean::cnstr_get(x_526, 2);
lean::inc(x_531);
lean::dec(x_526);
x_472 = x_527;
x_473 = x_529;
x_474 = x_531;
goto lbl_475;
}
else
{
obj* x_534; uint8 x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; obj* x_541; obj* x_542; obj* x_543; obj* x_544; obj* x_545; obj* x_546; 
x_534 = lean::cnstr_get(x_526, 0);
x_536 = lean::cnstr_get_scalar<uint8>(x_526, sizeof(void*)*1);
if (lean::is_exclusive(x_526)) {
 x_537 = x_526;
} else {
 lean::inc(x_534);
 lean::dec(x_526);
 x_537 = lean::box(0);
}
if (lean::is_scalar(x_537)) {
 x_538 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_538 = x_537;
}
lean::cnstr_set(x_538, 0, x_534);
lean::cnstr_set_scalar(x_538, sizeof(void*)*1, x_536);
x_539 = x_538;
x_540 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_539);
x_541 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_540);
x_542 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_541);
x_543 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_542);
x_544 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_543);
x_545 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_544);
x_546 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_545);
return x_546;
}
}
}
else
{
obj* x_548; uint8 x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
lean::dec(x_0);
x_548 = lean::cnstr_get(x_478, 0);
x_550 = lean::cnstr_get_scalar<uint8>(x_478, sizeof(void*)*1);
if (lean::is_exclusive(x_478)) {
 x_551 = x_478;
} else {
 lean::inc(x_548);
 lean::dec(x_478);
 x_551 = lean::box(0);
}
if (lean::is_scalar(x_551)) {
 x_552 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_552 = x_551;
}
lean::cnstr_set(x_552, 0, x_548);
lean::cnstr_set_scalar(x_552, sizeof(void*)*1, x_550);
x_553 = x_552;
x_554 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_553);
x_555 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_554);
x_556 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_555);
x_557 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_556);
x_558 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_557);
x_559 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_558);
x_560 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_559);
return x_560;
}
}
else
{
obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; 
lean::dec(x_387);
lean::dec(x_4);
lean::dec(x_0);
x_564 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_386);
x_565 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_564);
x_566 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_565);
x_567 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_566);
x_568 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_567);
x_569 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_568);
return x_569;
}
lbl_471:
{
obj* x_570; 
x_570 = l_lean_ir_parse__var(x_469);
lean::dec(x_469);
if (lean::obj_tag(x_570) == 0)
{
obj* x_572; obj* x_574; obj* x_576; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; obj* x_585; obj* x_586; obj* x_587; obj* x_588; obj* x_589; obj* x_590; 
x_572 = lean::cnstr_get(x_570, 0);
x_574 = lean::cnstr_get(x_570, 1);
x_576 = lean::cnstr_get(x_570, 2);
if (lean::is_exclusive(x_570)) {
 x_578 = x_570;
} else {
 lean::inc(x_572);
 lean::inc(x_574);
 lean::inc(x_576);
 lean::dec(x_570);
 x_578 = lean::box(0);
}
x_579 = lean::apply_1(x_468, x_572);
x_580 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_578)) {
 x_581 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_581 = x_578;
}
lean::cnstr_set(x_581, 0, x_579);
lean::cnstr_set(x_581, 1, x_574);
lean::cnstr_set(x_581, 2, x_580);
x_582 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_576, x_581);
x_583 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_470, x_582);
x_584 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_583);
x_585 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_584);
x_586 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_585);
x_587 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_586);
x_588 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_587);
x_589 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_588);
x_590 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_589);
return x_590;
}
else
{
obj* x_592; uint8 x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; 
lean::dec(x_468);
x_592 = lean::cnstr_get(x_570, 0);
x_594 = lean::cnstr_get_scalar<uint8>(x_570, sizeof(void*)*1);
if (lean::is_exclusive(x_570)) {
 x_595 = x_570;
} else {
 lean::inc(x_592);
 lean::dec(x_570);
 x_595 = lean::box(0);
}
if (lean::is_scalar(x_595)) {
 x_596 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_596 = x_595;
}
lean::cnstr_set(x_596, 0, x_592);
lean::cnstr_set_scalar(x_596, sizeof(void*)*1, x_594);
x_597 = x_596;
x_598 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_470, x_597);
x_599 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_598);
x_600 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_599);
x_601 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_600);
x_602 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_601);
x_603 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_602);
x_604 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_603);
x_605 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_604);
return x_605;
}
}
lbl_475:
{
obj* x_606; 
x_606 = l_lean_ir_parse__var(x_473);
lean::dec(x_473);
if (lean::obj_tag(x_606) == 0)
{
obj* x_608; obj* x_610; obj* x_612; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; obj* x_619; 
x_608 = lean::cnstr_get(x_606, 0);
x_610 = lean::cnstr_get(x_606, 1);
x_612 = lean::cnstr_get(x_606, 2);
if (lean::is_exclusive(x_606)) {
 x_614 = x_606;
} else {
 lean::inc(x_608);
 lean::inc(x_610);
 lean::inc(x_612);
 lean::dec(x_606);
 x_614 = lean::box(0);
}
x_615 = lean::apply_1(x_472, x_608);
x_616 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_614)) {
 x_617 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_617 = x_614;
}
lean::cnstr_set(x_617, 0, x_615);
lean::cnstr_set(x_617, 1, x_610);
lean::cnstr_set(x_617, 2, x_616);
x_618 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_612, x_617);
x_619 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_474, x_618);
if (lean::obj_tag(x_619) == 0)
{
obj* x_620; obj* x_622; obj* x_624; 
x_620 = lean::cnstr_get(x_619, 0);
lean::inc(x_620);
x_622 = lean::cnstr_get(x_619, 1);
lean::inc(x_622);
x_624 = lean::cnstr_get(x_619, 2);
lean::inc(x_624);
lean::dec(x_619);
x_468 = x_620;
x_469 = x_622;
x_470 = x_624;
goto lbl_471;
}
else
{
obj* x_627; uint8 x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_636; obj* x_637; obj* x_638; obj* x_639; 
x_627 = lean::cnstr_get(x_619, 0);
x_629 = lean::cnstr_get_scalar<uint8>(x_619, sizeof(void*)*1);
if (lean::is_exclusive(x_619)) {
 x_630 = x_619;
} else {
 lean::inc(x_627);
 lean::dec(x_619);
 x_630 = lean::box(0);
}
if (lean::is_scalar(x_630)) {
 x_631 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_631 = x_630;
}
lean::cnstr_set(x_631, 0, x_627);
lean::cnstr_set_scalar(x_631, sizeof(void*)*1, x_629);
x_632 = x_631;
x_633 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_632);
x_634 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_633);
x_635 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_634);
x_636 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_635);
x_637 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_636);
x_638 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_637);
x_639 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_638);
return x_639;
}
}
else
{
obj* x_641; uint8 x_643; obj* x_644; obj* x_645; obj* x_646; obj* x_647; 
lean::dec(x_472);
x_641 = lean::cnstr_get(x_606, 0);
x_643 = lean::cnstr_get_scalar<uint8>(x_606, sizeof(void*)*1);
if (lean::is_exclusive(x_606)) {
 x_644 = x_606;
} else {
 lean::inc(x_641);
 lean::dec(x_606);
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
x_647 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_474, x_646);
if (lean::obj_tag(x_647) == 0)
{
obj* x_648; obj* x_650; obj* x_652; 
x_648 = lean::cnstr_get(x_647, 0);
lean::inc(x_648);
x_650 = lean::cnstr_get(x_647, 1);
lean::inc(x_650);
x_652 = lean::cnstr_get(x_647, 2);
lean::inc(x_652);
lean::dec(x_647);
x_468 = x_648;
x_469 = x_650;
x_470 = x_652;
goto lbl_471;
}
else
{
obj* x_655; uint8 x_657; obj* x_658; obj* x_659; obj* x_660; obj* x_661; obj* x_662; obj* x_663; obj* x_664; obj* x_665; obj* x_666; obj* x_667; 
x_655 = lean::cnstr_get(x_647, 0);
x_657 = lean::cnstr_get_scalar<uint8>(x_647, sizeof(void*)*1);
if (lean::is_exclusive(x_647)) {
 x_658 = x_647;
} else {
 lean::inc(x_655);
 lean::dec(x_647);
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
x_661 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_387, x_660);
x_662 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_661);
x_663 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_662);
x_664 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_663);
x_665 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_664);
x_666 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_665);
x_667 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_666);
return x_667;
}
}
}
}
lbl_393:
{
obj* x_668; 
x_668 = l_lean_ir_parse__var(x_391);
lean::dec(x_391);
if (lean::obj_tag(x_668) == 0)
{
obj* x_670; obj* x_672; obj* x_674; obj* x_676; obj* x_677; obj* x_678; obj* x_679; obj* x_680; obj* x_681; 
x_670 = lean::cnstr_get(x_668, 0);
x_672 = lean::cnstr_get(x_668, 1);
x_674 = lean::cnstr_get(x_668, 2);
if (lean::is_exclusive(x_668)) {
 x_676 = x_668;
} else {
 lean::inc(x_670);
 lean::inc(x_672);
 lean::inc(x_674);
 lean::dec(x_668);
 x_676 = lean::box(0);
}
x_677 = lean::apply_1(x_390, x_670);
x_678 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_676)) {
 x_679 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_679 = x_676;
}
lean::cnstr_set(x_679, 0, x_677);
lean::cnstr_set(x_679, 1, x_672);
lean::cnstr_set(x_679, 2, x_678);
x_680 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_674, x_679);
x_681 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_392, x_680);
if (lean::obj_tag(x_681) == 0)
{
obj* x_684; obj* x_685; obj* x_686; obj* x_687; obj* x_688; obj* x_689; 
lean::dec(x_4);
lean::dec(x_0);
x_684 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_681);
x_685 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_684);
x_686 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_685);
x_687 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_686);
x_688 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_687);
x_689 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_688);
return x_689;
}
else
{
obj* x_690; uint8 x_692; 
x_690 = lean::cnstr_get(x_681, 0);
lean::inc(x_690);
x_692 = lean::cnstr_get_scalar<uint8>(x_681, sizeof(void*)*1);
x_386 = x_681;
x_387 = x_690;
x_388 = x_692;
goto lbl_389;
}
}
else
{
obj* x_694; uint8 x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; 
lean::dec(x_390);
x_694 = lean::cnstr_get(x_668, 0);
x_696 = lean::cnstr_get_scalar<uint8>(x_668, sizeof(void*)*1);
if (lean::is_exclusive(x_668)) {
 x_697 = x_668;
} else {
 lean::inc(x_694);
 lean::dec(x_668);
 x_697 = lean::box(0);
}
if (lean::is_scalar(x_697)) {
 x_698 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_698 = x_697;
}
lean::cnstr_set(x_698, 0, x_694);
lean::cnstr_set_scalar(x_698, sizeof(void*)*1, x_696);
x_699 = x_698;
x_700 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_392, x_699);
if (lean::obj_tag(x_700) == 0)
{
obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; 
lean::dec(x_4);
lean::dec(x_0);
x_703 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_303, x_700);
x_704 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_703);
x_705 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_704);
x_706 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_705);
x_707 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_706);
x_708 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_707);
return x_708;
}
else
{
obj* x_709; uint8 x_711; 
x_709 = lean::cnstr_get(x_700, 0);
lean::inc(x_709);
x_711 = lean::cnstr_get_scalar<uint8>(x_700, sizeof(void*)*1);
x_386 = x_700;
x_387 = x_709;
x_388 = x_711;
goto lbl_389;
}
}
}
}
lbl_309:
{
obj* x_712; 
x_712 = l_lean_ir_parse__usize(x_307);
if (lean::obj_tag(x_712) == 0)
{
obj* x_713; obj* x_715; obj* x_717; obj* x_719; obj* x_720; obj* x_721; obj* x_722; obj* x_723; obj* x_724; 
x_713 = lean::cnstr_get(x_712, 0);
x_715 = lean::cnstr_get(x_712, 1);
x_717 = lean::cnstr_get(x_712, 2);
if (lean::is_exclusive(x_712)) {
 x_719 = x_712;
} else {
 lean::inc(x_713);
 lean::inc(x_715);
 lean::inc(x_717);
 lean::dec(x_712);
 x_719 = lean::box(0);
}
x_720 = lean::apply_1(x_306, x_713);
x_721 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_719)) {
 x_722 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_722 = x_719;
}
lean::cnstr_set(x_722, 0, x_720);
lean::cnstr_set(x_722, 1, x_715);
lean::cnstr_set(x_722, 2, x_721);
x_723 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_717, x_722);
x_724 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_723);
if (lean::obj_tag(x_724) == 0)
{
obj* x_727; obj* x_728; obj* x_729; obj* x_730; obj* x_731; 
lean::dec(x_4);
lean::dec(x_0);
x_727 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_724);
x_728 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_727);
x_729 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_728);
x_730 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_729);
x_731 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_730);
return x_731;
}
else
{
obj* x_732; uint8 x_734; 
x_732 = lean::cnstr_get(x_724, 0);
lean::inc(x_732);
x_734 = lean::cnstr_get_scalar<uint8>(x_724, sizeof(void*)*1);
x_302 = x_724;
x_303 = x_732;
x_304 = x_734;
goto lbl_305;
}
}
else
{
obj* x_736; uint8 x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
lean::dec(x_306);
x_736 = lean::cnstr_get(x_712, 0);
x_738 = lean::cnstr_get_scalar<uint8>(x_712, sizeof(void*)*1);
if (lean::is_exclusive(x_712)) {
 x_739 = x_712;
} else {
 lean::inc(x_736);
 lean::dec(x_712);
 x_739 = lean::box(0);
}
if (lean::is_scalar(x_739)) {
 x_740 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_740 = x_739;
}
lean::cnstr_set(x_740, 0, x_736);
lean::cnstr_set_scalar(x_740, sizeof(void*)*1, x_738);
x_741 = x_740;
x_742 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_741);
if (lean::obj_tag(x_742) == 0)
{
obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; 
lean::dec(x_4);
lean::dec(x_0);
x_745 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_223, x_742);
x_746 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_745);
x_747 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_746);
x_748 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_747);
x_749 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_748);
return x_749;
}
else
{
obj* x_750; uint8 x_752; 
x_750 = lean::cnstr_get(x_742, 0);
lean::inc(x_750);
x_752 = lean::cnstr_get_scalar<uint8>(x_742, sizeof(void*)*1);
x_302 = x_742;
x_303 = x_750;
x_304 = x_752;
goto lbl_305;
}
}
}
lbl_313:
{
obj* x_753; 
x_753 = l_lean_ir_parse__uint16(x_311);
if (lean::obj_tag(x_753) == 0)
{
obj* x_754; obj* x_756; obj* x_758; obj* x_760; obj* x_761; obj* x_762; obj* x_763; obj* x_764; obj* x_765; 
x_754 = lean::cnstr_get(x_753, 0);
x_756 = lean::cnstr_get(x_753, 1);
x_758 = lean::cnstr_get(x_753, 2);
if (lean::is_exclusive(x_753)) {
 x_760 = x_753;
} else {
 lean::inc(x_754);
 lean::inc(x_756);
 lean::inc(x_758);
 lean::dec(x_753);
 x_760 = lean::box(0);
}
x_761 = lean::apply_1(x_310, x_754);
x_762 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_760)) {
 x_763 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_763 = x_760;
}
lean::cnstr_set(x_763, 0, x_761);
lean::cnstr_set(x_763, 1, x_756);
lean::cnstr_set(x_763, 2, x_762);
x_764 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_758, x_763);
x_765 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_312, x_764);
if (lean::obj_tag(x_765) == 0)
{
obj* x_766; obj* x_768; obj* x_770; 
x_766 = lean::cnstr_get(x_765, 0);
lean::inc(x_766);
x_768 = lean::cnstr_get(x_765, 1);
lean::inc(x_768);
x_770 = lean::cnstr_get(x_765, 2);
lean::inc(x_770);
lean::dec(x_765);
x_306 = x_766;
x_307 = x_768;
x_308 = x_770;
goto lbl_309;
}
else
{
obj* x_773; uint8 x_775; obj* x_776; obj* x_778; obj* x_779; 
x_773 = lean::cnstr_get(x_765, 0);
x_775 = lean::cnstr_get_scalar<uint8>(x_765, sizeof(void*)*1);
if (lean::is_exclusive(x_765)) {
 x_776 = x_765;
} else {
 lean::inc(x_773);
 lean::dec(x_765);
 x_776 = lean::box(0);
}
lean::inc(x_773);
if (lean::is_scalar(x_776)) {
 x_778 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_778 = x_776;
}
lean::cnstr_set(x_778, 0, x_773);
lean::cnstr_set_scalar(x_778, sizeof(void*)*1, x_775);
x_779 = x_778;
x_302 = x_779;
x_303 = x_773;
x_304 = x_775;
goto lbl_305;
}
}
else
{
obj* x_781; uint8 x_783; obj* x_784; obj* x_785; obj* x_786; obj* x_787; 
lean::dec(x_310);
x_781 = lean::cnstr_get(x_753, 0);
x_783 = lean::cnstr_get_scalar<uint8>(x_753, sizeof(void*)*1);
if (lean::is_exclusive(x_753)) {
 x_784 = x_753;
} else {
 lean::inc(x_781);
 lean::dec(x_753);
 x_784 = lean::box(0);
}
if (lean::is_scalar(x_784)) {
 x_785 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_785 = x_784;
}
lean::cnstr_set(x_785, 0, x_781);
lean::cnstr_set_scalar(x_785, sizeof(void*)*1, x_783);
x_786 = x_785;
x_787 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_312, x_786);
if (lean::obj_tag(x_787) == 0)
{
obj* x_788; obj* x_790; obj* x_792; 
x_788 = lean::cnstr_get(x_787, 0);
lean::inc(x_788);
x_790 = lean::cnstr_get(x_787, 1);
lean::inc(x_790);
x_792 = lean::cnstr_get(x_787, 2);
lean::inc(x_792);
lean::dec(x_787);
x_306 = x_788;
x_307 = x_790;
x_308 = x_792;
goto lbl_309;
}
else
{
obj* x_795; uint8 x_797; obj* x_798; obj* x_800; obj* x_801; 
x_795 = lean::cnstr_get(x_787, 0);
x_797 = lean::cnstr_get_scalar<uint8>(x_787, sizeof(void*)*1);
if (lean::is_exclusive(x_787)) {
 x_798 = x_787;
} else {
 lean::inc(x_795);
 lean::dec(x_787);
 x_798 = lean::box(0);
}
lean::inc(x_795);
if (lean::is_scalar(x_798)) {
 x_800 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_800 = x_798;
}
lean::cnstr_set(x_800, 0, x_795);
lean::cnstr_set_scalar(x_800, sizeof(void*)*1, x_797);
x_801 = x_800;
x_302 = x_801;
x_303 = x_795;
x_304 = x_797;
goto lbl_305;
}
}
}
}
lbl_229:
{
obj* x_802; 
x_802 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(x_227);
lean::dec(x_227);
if (lean::obj_tag(x_802) == 0)
{
obj* x_804; obj* x_806; obj* x_808; obj* x_810; obj* x_811; obj* x_812; obj* x_813; obj* x_814; obj* x_815; 
x_804 = lean::cnstr_get(x_802, 0);
x_806 = lean::cnstr_get(x_802, 1);
x_808 = lean::cnstr_get(x_802, 2);
if (lean::is_exclusive(x_802)) {
 x_810 = x_802;
} else {
 lean::inc(x_804);
 lean::inc(x_806);
 lean::inc(x_808);
 lean::dec(x_802);
 x_810 = lean::box(0);
}
x_811 = lean::apply_1(x_226, x_804);
x_812 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_810)) {
 x_813 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_813 = x_810;
}
lean::cnstr_set(x_813, 0, x_811);
lean::cnstr_set(x_813, 1, x_806);
lean::cnstr_set(x_813, 2, x_812);
x_814 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_808, x_813);
x_815 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_228, x_814);
if (lean::obj_tag(x_815) == 0)
{
obj* x_818; obj* x_819; obj* x_820; obj* x_821; 
lean::dec(x_4);
lean::dec(x_0);
x_818 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_815);
x_819 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_818);
x_820 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_819);
x_821 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_820);
return x_821;
}
else
{
obj* x_822; uint8 x_824; 
x_822 = lean::cnstr_get(x_815, 0);
lean::inc(x_822);
x_824 = lean::cnstr_get_scalar<uint8>(x_815, sizeof(void*)*1);
x_222 = x_815;
x_223 = x_822;
x_224 = x_824;
goto lbl_225;
}
}
else
{
obj* x_826; uint8 x_828; obj* x_829; obj* x_830; obj* x_831; obj* x_832; 
lean::dec(x_226);
x_826 = lean::cnstr_get(x_802, 0);
x_828 = lean::cnstr_get_scalar<uint8>(x_802, sizeof(void*)*1);
if (lean::is_exclusive(x_802)) {
 x_829 = x_802;
} else {
 lean::inc(x_826);
 lean::dec(x_802);
 x_829 = lean::box(0);
}
if (lean::is_scalar(x_829)) {
 x_830 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_830 = x_829;
}
lean::cnstr_set(x_830, 0, x_826);
lean::cnstr_set_scalar(x_830, sizeof(void*)*1, x_828);
x_831 = x_830;
x_832 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_228, x_831);
if (lean::obj_tag(x_832) == 0)
{
obj* x_835; obj* x_836; obj* x_837; obj* x_838; 
lean::dec(x_4);
lean::dec(x_0);
x_835 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_144, x_832);
x_836 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_835);
x_837 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_836);
x_838 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_837);
return x_838;
}
else
{
obj* x_839; uint8 x_841; 
x_839 = lean::cnstr_get(x_832, 0);
lean::inc(x_839);
x_841 = lean::cnstr_get_scalar<uint8>(x_832, sizeof(void*)*1);
x_222 = x_832;
x_223 = x_839;
x_224 = x_841;
goto lbl_225;
}
}
}
}
lbl_150:
{
obj* x_842; 
x_842 = l_lean_ir_parse__uint16(x_148);
if (lean::obj_tag(x_842) == 0)
{
obj* x_843; obj* x_845; obj* x_847; obj* x_849; obj* x_850; obj* x_851; obj* x_852; obj* x_853; obj* x_854; 
x_843 = lean::cnstr_get(x_842, 0);
x_845 = lean::cnstr_get(x_842, 1);
x_847 = lean::cnstr_get(x_842, 2);
if (lean::is_exclusive(x_842)) {
 x_849 = x_842;
} else {
 lean::inc(x_843);
 lean::inc(x_845);
 lean::inc(x_847);
 lean::dec(x_842);
 x_849 = lean::box(0);
}
x_850 = lean::apply_1(x_147, x_843);
x_851 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_849)) {
 x_852 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_852 = x_849;
}
lean::cnstr_set(x_852, 0, x_850);
lean::cnstr_set(x_852, 1, x_845);
lean::cnstr_set(x_852, 2, x_851);
x_853 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_847, x_852);
x_854 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_149, x_853);
if (lean::obj_tag(x_854) == 0)
{
obj* x_857; obj* x_858; obj* x_859; 
lean::dec(x_4);
lean::dec(x_0);
x_857 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_854);
x_858 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_857);
x_859 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_858);
return x_859;
}
else
{
obj* x_860; uint8 x_862; 
x_860 = lean::cnstr_get(x_854, 0);
lean::inc(x_860);
x_862 = lean::cnstr_get_scalar<uint8>(x_854, sizeof(void*)*1);
x_143 = x_854;
x_144 = x_860;
x_145 = x_862;
goto lbl_146;
}
}
else
{
obj* x_864; uint8 x_866; obj* x_867; obj* x_868; obj* x_869; obj* x_870; 
lean::dec(x_147);
x_864 = lean::cnstr_get(x_842, 0);
x_866 = lean::cnstr_get_scalar<uint8>(x_842, sizeof(void*)*1);
if (lean::is_exclusive(x_842)) {
 x_867 = x_842;
} else {
 lean::inc(x_864);
 lean::dec(x_842);
 x_867 = lean::box(0);
}
if (lean::is_scalar(x_867)) {
 x_868 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_868 = x_867;
}
lean::cnstr_set(x_868, 0, x_864);
lean::cnstr_set_scalar(x_868, sizeof(void*)*1, x_866);
x_869 = x_868;
x_870 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_149, x_869);
if (lean::obj_tag(x_870) == 0)
{
obj* x_873; obj* x_874; obj* x_875; 
lean::dec(x_4);
lean::dec(x_0);
x_873 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_84, x_870);
x_874 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_80, x_873);
x_875 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_874);
return x_875;
}
else
{
obj* x_876; uint8 x_878; 
x_876 = lean::cnstr_get(x_870, 0);
lean::inc(x_876);
x_878 = lean::cnstr_get_scalar<uint8>(x_870, sizeof(void*)*1);
x_143 = x_870;
x_144 = x_876;
x_145 = x_878;
goto lbl_146;
}
}
}
}
}
}
lbl_14:
{
obj* x_879; 
x_879 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(x_12);
lean::dec(x_12);
if (lean::obj_tag(x_879) == 0)
{
obj* x_881; obj* x_883; obj* x_885; obj* x_887; obj* x_888; obj* x_889; obj* x_890; obj* x_891; obj* x_892; 
x_881 = lean::cnstr_get(x_879, 0);
x_883 = lean::cnstr_get(x_879, 1);
x_885 = lean::cnstr_get(x_879, 2);
if (lean::is_exclusive(x_879)) {
 x_887 = x_879;
} else {
 lean::inc(x_881);
 lean::inc(x_883);
 lean::inc(x_885);
 lean::dec(x_879);
 x_887 = lean::box(0);
}
x_888 = lean::apply_1(x_11, x_881);
x_889 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_887)) {
 x_890 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_890 = x_887;
}
lean::cnstr_set(x_890, 0, x_888);
lean::cnstr_set(x_890, 1, x_883);
lean::cnstr_set(x_890, 2, x_889);
x_891 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_885, x_890);
x_892 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_891);
x_9 = x_892;
goto lbl_10;
}
else
{
obj* x_894; uint8 x_896; obj* x_897; obj* x_898; obj* x_899; obj* x_900; 
lean::dec(x_11);
x_894 = lean::cnstr_get(x_879, 0);
x_896 = lean::cnstr_get_scalar<uint8>(x_879, sizeof(void*)*1);
if (lean::is_exclusive(x_879)) {
 x_897 = x_879;
} else {
 lean::inc(x_894);
 lean::dec(x_879);
 x_897 = lean::box(0);
}
if (lean::is_scalar(x_897)) {
 x_898 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_898 = x_897;
}
lean::cnstr_set(x_898, 0, x_894);
lean::cnstr_set_scalar(x_898, sizeof(void*)*1, x_896);
x_899 = x_898;
x_900 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_899);
x_9 = x_900;
goto lbl_10;
}
}
}
else
{
obj* x_902; uint8 x_904; obj* x_905; obj* x_906; obj* x_907; 
lean::dec(x_0);
x_902 = lean::cnstr_get(x_3, 0);
x_904 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_905 = x_3;
} else {
 lean::inc(x_902);
 lean::dec(x_3);
 x_905 = lean::box(0);
}
if (lean::is_scalar(x_905)) {
 x_906 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_906 = x_905;
}
lean::cnstr_set(x_906, 0, x_902);
lean::cnstr_set_scalar(x_906, sizeof(void*)*1, x_904);
x_907 = x_906;
return x_907;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__untyped__assignment___spec__8(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__untyped__assignment___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__untyped__assignment___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_parse__untyped__assignment___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__untyped__assignment___lambda__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::dec(x_0);
return x_7;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__untyped__assignment___lambda__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_lean_ir_parse__untyped__assignment___lambda__5(x_0, x_1, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_parse__untyped__assignment___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__untyped__assignment___lambda__6(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* l_lean_ir_parse__assignment___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__assignment(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__instr___lambda__1(uint8 x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = lean::alloc_cnstr(4, 1, 1);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_0);
x_4 = x_3;
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__2(obj* x_0, usize x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(9, 2, sizeof(size_t)*1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_1);
x_6 = x_5;
return x_6;
}
}
obj* l_lean_ir_parse__instr___lambda__3(obj* x_0, uint16 x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(7, 2, 2);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_1);
x_6 = x_5;
return x_6;
}
}
obj* l_lean_ir_parse__instr___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(15, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
return x_6;
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
lean::dec(x_14);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_21 = lean::cnstr_get(x_19, 0);
x_23 = lean::cnstr_get(x_19, 1);
x_25 = lean::cnstr_get(x_19, 2);
if (lean::is_exclusive(x_19)) {
 x_27 = x_19;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_19);
 x_27 = lean::box(0);
}
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__4___boxed), 3, 1);
lean::closure_set(x_28, 0, x_21);
x_29 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_27)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_27;
}
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_23);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_35; obj* x_37; 
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_32, 2);
lean::inc(x_37);
lean::dec(x_32);
x_7 = x_33;
x_8 = x_35;
x_9 = x_37;
goto lbl_10;
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_32, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_exclusive(x_32)) {
 x_43 = x_32;
} else {
 lean::inc(x_40);
 lean::dec(x_32);
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
x_1 = x_45;
goto lbl_2;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
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
obj* x_89; obj* x_91; 
lean::dec(x_1);
x_89 = l_lean_ir_parse__instr___closed__2;
lean::inc(x_0);
x_91 = l_lean_ir_keyword(x_89, x_0);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_94; obj* x_97; 
x_92 = lean::cnstr_get(x_91, 1);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 2);
lean::inc(x_94);
lean::dec(x_91);
x_97 = l_lean_ir_parse__var(x_92);
lean::dec(x_92);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_101; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_97, 0);
x_101 = lean::cnstr_get(x_97, 1);
x_103 = lean::cnstr_get(x_97, 2);
if (lean::is_exclusive(x_97)) {
 x_105 = x_97;
} else {
 lean::inc(x_99);
 lean::inc(x_101);
 lean::inc(x_103);
 lean::dec(x_97);
 x_105 = lean::box(0);
}
x_106 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__3___boxed), 3, 1);
lean::closure_set(x_106, 0, x_99);
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
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_113; obj* x_115; 
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_110, 2);
lean::inc(x_115);
lean::dec(x_110);
x_84 = x_111;
x_85 = x_113;
x_86 = x_115;
goto lbl_87;
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_123; obj* x_124; 
x_118 = lean::cnstr_get(x_110, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
if (lean::is_exclusive(x_110)) {
 x_121 = x_110;
} else {
 lean::inc(x_118);
 lean::dec(x_110);
 x_121 = lean::box(0);
}
lean::inc(x_118);
if (lean::is_scalar(x_121)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_121;
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
obj* x_125; uint8 x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_125 = lean::cnstr_get(x_97, 0);
x_127 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
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
obj* x_171; obj* x_173; obj* x_176; 
x_171 = lean::cnstr_get(x_170, 1);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_170, 2);
lean::inc(x_173);
lean::dec(x_170);
x_176 = l_lean_ir_parse__var(x_171);
lean::dec(x_171);
if (lean::obj_tag(x_176) == 0)
{
obj* x_178; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
x_178 = lean::cnstr_get(x_176, 0);
x_180 = lean::cnstr_get(x_176, 1);
x_182 = lean::cnstr_get(x_176, 2);
if (lean::is_exclusive(x_176)) {
 x_184 = x_176;
} else {
 lean::inc(x_178);
 lean::inc(x_180);
 lean::inc(x_182);
 lean::dec(x_176);
 x_184 = lean::box(0);
}
x_185 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__instr___lambda__2___boxed), 3, 1);
lean::closure_set(x_185, 0, x_178);
x_186 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_184)) {
 x_187 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_187 = x_184;
}
lean::cnstr_set(x_187, 0, x_185);
lean::cnstr_set(x_187, 1, x_180);
lean::cnstr_set(x_187, 2, x_186);
x_188 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_187);
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_188);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; obj* x_192; obj* x_194; 
x_190 = lean::cnstr_get(x_189, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_189, 2);
lean::inc(x_194);
lean::dec(x_189);
x_163 = x_190;
x_164 = x_192;
x_165 = x_194;
goto lbl_166;
}
else
{
obj* x_197; uint8 x_199; obj* x_200; obj* x_202; obj* x_203; 
x_197 = lean::cnstr_get(x_189, 0);
x_199 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*1);
if (lean::is_exclusive(x_189)) {
 x_200 = x_189;
} else {
 lean::inc(x_197);
 lean::dec(x_189);
 x_200 = lean::box(0);
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
x_155 = x_203;
x_156 = x_197;
x_157 = x_199;
goto lbl_158;
}
}
else
{
obj* x_204; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_204 = lean::cnstr_get(x_176, 0);
x_206 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_exclusive(x_176)) {
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
obj* x_267; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_265);
x_267 = l_lean_ir_parse__assignment(x_0);
lean::dec(x_0);
x_269 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_262, x_267);
x_270 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_269);
x_271 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_270);
x_272 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_271);
return x_272;
}
else
{
obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
lean::dec(x_0);
if (lean::is_scalar(x_265)) {
 x_274 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_274 = x_265;
}
lean::cnstr_set(x_274, 0, x_262);
lean::cnstr_set_scalar(x_274, sizeof(void*)*1, x_264);
x_275 = x_274;
x_276 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_275);
x_277 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_276);
x_278 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_277);
return x_278;
}
}
}
else
{
obj* x_279; uint8 x_281; obj* x_282; 
x_279 = lean::cnstr_get(x_243, 0);
x_281 = lean::cnstr_get_scalar<uint8>(x_243, sizeof(void*)*1);
if (lean::is_exclusive(x_243)) {
 lean::cnstr_set(x_243, 0, lean::box(0));
 x_282 = x_243;
} else {
 lean::inc(x_279);
 lean::dec(x_243);
 x_282 = lean::box(0);
}
if (x_281 == 0)
{
obj* x_284; obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_282);
x_284 = l_lean_ir_parse__assignment(x_0);
lean::dec(x_0);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_279, x_284);
x_287 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_286);
x_288 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_287);
x_289 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_288);
return x_289;
}
else
{
obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_0);
if (lean::is_scalar(x_282)) {
 x_291 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_291 = x_282;
}
lean::cnstr_set(x_291, 0, x_279);
lean::cnstr_set_scalar(x_291, sizeof(void*)*1, x_281);
x_292 = x_291;
x_293 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_292);
x_294 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_293);
x_295 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_294);
return x_295;
}
}
}
else
{
obj* x_298; obj* x_299; 
lean::dec(x_156);
lean::dec(x_0);
x_298 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_155);
x_299 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_298);
return x_299;
}
lbl_238:
{
obj* x_300; 
x_300 = l_lean_ir_parse__var(x_236);
lean::dec(x_236);
if (lean::obj_tag(x_300) == 0)
{
obj* x_302; obj* x_304; obj* x_306; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; 
x_302 = lean::cnstr_get(x_300, 0);
x_304 = lean::cnstr_get(x_300, 1);
x_306 = lean::cnstr_get(x_300, 2);
if (lean::is_exclusive(x_300)) {
 x_308 = x_300;
} else {
 lean::inc(x_302);
 lean::inc(x_304);
 lean::inc(x_306);
 lean::dec(x_300);
 x_308 = lean::box(0);
}
x_309 = lean::apply_1(x_235, x_302);
x_310 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_308)) {
 x_311 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_311 = x_308;
}
lean::cnstr_set(x_311, 0, x_309);
lean::cnstr_set(x_311, 1, x_304);
lean::cnstr_set(x_311, 2, x_310);
x_312 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_306, x_311);
x_313 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_237, x_312);
if (lean::obj_tag(x_313) == 0)
{
obj* x_315; obj* x_316; obj* x_317; 
lean::dec(x_0);
x_315 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_313);
x_316 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_315);
x_317 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_316);
return x_317;
}
else
{
obj* x_318; uint8 x_320; 
x_318 = lean::cnstr_get(x_313, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get_scalar<uint8>(x_313, sizeof(void*)*1);
if (x_320 == 0)
{
obj* x_322; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
lean::dec(x_313);
x_322 = l_lean_ir_parse__assignment(x_0);
lean::dec(x_0);
x_324 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_318, x_322);
x_325 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_324);
x_326 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_325);
x_327 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_326);
return x_327;
}
else
{
obj* x_330; obj* x_331; obj* x_332; 
lean::dec(x_0);
lean::dec(x_318);
x_330 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_313);
x_331 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_330);
x_332 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_331);
return x_332;
}
}
}
else
{
obj* x_334; uint8 x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; 
lean::dec(x_235);
x_334 = lean::cnstr_get(x_300, 0);
x_336 = lean::cnstr_get_scalar<uint8>(x_300, sizeof(void*)*1);
if (lean::is_exclusive(x_300)) {
 x_337 = x_300;
} else {
 lean::inc(x_334);
 lean::dec(x_300);
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
x_340 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_237, x_339);
if (lean::obj_tag(x_340) == 0)
{
obj* x_342; obj* x_343; obj* x_344; 
lean::dec(x_0);
x_342 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_340);
x_343 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_342);
x_344 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_343);
return x_344;
}
else
{
obj* x_345; uint8 x_347; 
x_345 = lean::cnstr_get(x_340, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get_scalar<uint8>(x_340, sizeof(void*)*1);
if (x_347 == 0)
{
obj* x_349; obj* x_351; obj* x_352; obj* x_353; obj* x_354; 
lean::dec(x_340);
x_349 = l_lean_ir_parse__assignment(x_0);
lean::dec(x_0);
x_351 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_345, x_349);
x_352 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_351);
x_353 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_352);
x_354 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_353);
return x_354;
}
else
{
obj* x_357; obj* x_358; obj* x_359; 
lean::dec(x_0);
lean::dec(x_345);
x_357 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_156, x_340);
x_358 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_357);
x_359 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_358);
return x_359;
}
}
}
}
}
lbl_162:
{
obj* x_360; 
x_360 = l_lean_ir_parse__var(x_160);
lean::dec(x_160);
if (lean::obj_tag(x_360) == 0)
{
obj* x_362; obj* x_364; obj* x_366; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; 
x_362 = lean::cnstr_get(x_360, 0);
x_364 = lean::cnstr_get(x_360, 1);
x_366 = lean::cnstr_get(x_360, 2);
if (lean::is_exclusive(x_360)) {
 x_368 = x_360;
} else {
 lean::inc(x_362);
 lean::inc(x_364);
 lean::inc(x_366);
 lean::dec(x_360);
 x_368 = lean::box(0);
}
x_369 = lean::apply_1(x_159, x_362);
x_370 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_368)) {
 x_371 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_371 = x_368;
}
lean::cnstr_set(x_371, 0, x_369);
lean::cnstr_set(x_371, 1, x_364);
lean::cnstr_set(x_371, 2, x_370);
x_372 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_366, x_371);
x_373 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_372);
if (lean::obj_tag(x_373) == 0)
{
obj* x_375; obj* x_376; 
lean::dec(x_0);
x_375 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_373);
x_376 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_375);
return x_376;
}
else
{
obj* x_377; uint8 x_379; 
x_377 = lean::cnstr_get(x_373, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get_scalar<uint8>(x_373, sizeof(void*)*1);
x_155 = x_373;
x_156 = x_377;
x_157 = x_379;
goto lbl_158;
}
}
else
{
obj* x_381; uint8 x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
lean::dec(x_159);
x_381 = lean::cnstr_get(x_360, 0);
x_383 = lean::cnstr_get_scalar<uint8>(x_360, sizeof(void*)*1);
if (lean::is_exclusive(x_360)) {
 x_384 = x_360;
} else {
 lean::inc(x_381);
 lean::dec(x_360);
 x_384 = lean::box(0);
}
if (lean::is_scalar(x_384)) {
 x_385 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_385 = x_384;
}
lean::cnstr_set(x_385, 0, x_381);
lean::cnstr_set_scalar(x_385, sizeof(void*)*1, x_383);
x_386 = x_385;
x_387 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_386);
if (lean::obj_tag(x_387) == 0)
{
obj* x_389; obj* x_390; 
lean::dec(x_0);
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_77, x_387);
x_390 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_389);
return x_390;
}
else
{
obj* x_391; uint8 x_393; 
x_391 = lean::cnstr_get(x_387, 0);
lean::inc(x_391);
x_393 = lean::cnstr_get_scalar<uint8>(x_387, sizeof(void*)*1);
x_155 = x_387;
x_156 = x_391;
x_157 = x_393;
goto lbl_158;
}
}
}
lbl_166:
{
obj* x_394; 
x_394 = l_lean_ir_parse__usize(x_164);
if (lean::obj_tag(x_394) == 0)
{
obj* x_395; obj* x_397; obj* x_399; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; 
x_395 = lean::cnstr_get(x_394, 0);
x_397 = lean::cnstr_get(x_394, 1);
x_399 = lean::cnstr_get(x_394, 2);
if (lean::is_exclusive(x_394)) {
 x_401 = x_394;
} else {
 lean::inc(x_395);
 lean::inc(x_397);
 lean::inc(x_399);
 lean::dec(x_394);
 x_401 = lean::box(0);
}
x_402 = lean::apply_1(x_163, x_395);
x_403 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_401)) {
 x_404 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_404 = x_401;
}
lean::cnstr_set(x_404, 0, x_402);
lean::cnstr_set(x_404, 1, x_397);
lean::cnstr_set(x_404, 2, x_403);
x_405 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_399, x_404);
x_406 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_405);
if (lean::obj_tag(x_406) == 0)
{
obj* x_407; obj* x_409; obj* x_411; 
x_407 = lean::cnstr_get(x_406, 0);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_406, 1);
lean::inc(x_409);
x_411 = lean::cnstr_get(x_406, 2);
lean::inc(x_411);
lean::dec(x_406);
x_159 = x_407;
x_160 = x_409;
x_161 = x_411;
goto lbl_162;
}
else
{
obj* x_414; uint8 x_416; obj* x_417; obj* x_419; obj* x_420; 
x_414 = lean::cnstr_get(x_406, 0);
x_416 = lean::cnstr_get_scalar<uint8>(x_406, sizeof(void*)*1);
if (lean::is_exclusive(x_406)) {
 x_417 = x_406;
} else {
 lean::inc(x_414);
 lean::dec(x_406);
 x_417 = lean::box(0);
}
lean::inc(x_414);
if (lean::is_scalar(x_417)) {
 x_419 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_419 = x_417;
}
lean::cnstr_set(x_419, 0, x_414);
lean::cnstr_set_scalar(x_419, sizeof(void*)*1, x_416);
x_420 = x_419;
x_155 = x_420;
x_156 = x_414;
x_157 = x_416;
goto lbl_158;
}
}
else
{
obj* x_422; uint8 x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_163);
x_422 = lean::cnstr_get(x_394, 0);
x_424 = lean::cnstr_get_scalar<uint8>(x_394, sizeof(void*)*1);
if (lean::is_exclusive(x_394)) {
 x_425 = x_394;
} else {
 lean::inc(x_422);
 lean::dec(x_394);
 x_425 = lean::box(0);
}
if (lean::is_scalar(x_425)) {
 x_426 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_426 = x_425;
}
lean::cnstr_set(x_426, 0, x_422);
lean::cnstr_set_scalar(x_426, sizeof(void*)*1, x_424);
x_427 = x_426;
x_428 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_427);
if (lean::obj_tag(x_428) == 0)
{
obj* x_429; obj* x_431; obj* x_433; 
x_429 = lean::cnstr_get(x_428, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_428, 1);
lean::inc(x_431);
x_433 = lean::cnstr_get(x_428, 2);
lean::inc(x_433);
lean::dec(x_428);
x_159 = x_429;
x_160 = x_431;
x_161 = x_433;
goto lbl_162;
}
else
{
obj* x_436; uint8 x_438; obj* x_439; obj* x_441; obj* x_442; 
x_436 = lean::cnstr_get(x_428, 0);
x_438 = lean::cnstr_get_scalar<uint8>(x_428, sizeof(void*)*1);
if (lean::is_exclusive(x_428)) {
 x_439 = x_428;
} else {
 lean::inc(x_436);
 lean::dec(x_428);
 x_439 = lean::box(0);
}
lean::inc(x_436);
if (lean::is_scalar(x_439)) {
 x_441 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_441 = x_439;
}
lean::cnstr_set(x_441, 0, x_436);
lean::cnstr_set_scalar(x_441, sizeof(void*)*1, x_438);
x_442 = x_441;
x_155 = x_442;
x_156 = x_436;
x_157 = x_438;
goto lbl_158;
}
}
}
}
lbl_83:
{
obj* x_443; 
x_443 = l_lean_ir_parse__var(x_81);
lean::dec(x_81);
if (lean::obj_tag(x_443) == 0)
{
obj* x_445; obj* x_447; obj* x_449; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; 
x_445 = lean::cnstr_get(x_443, 0);
x_447 = lean::cnstr_get(x_443, 1);
x_449 = lean::cnstr_get(x_443, 2);
if (lean::is_exclusive(x_443)) {
 x_451 = x_443;
} else {
 lean::inc(x_445);
 lean::inc(x_447);
 lean::inc(x_449);
 lean::dec(x_443);
 x_451 = lean::box(0);
}
x_452 = lean::apply_1(x_80, x_445);
x_453 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_451)) {
 x_454 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_454 = x_451;
}
lean::cnstr_set(x_454, 0, x_452);
lean::cnstr_set(x_454, 1, x_447);
lean::cnstr_set(x_454, 2, x_453);
x_455 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_449, x_454);
x_456 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_455);
if (lean::obj_tag(x_456) == 0)
{
obj* x_458; 
lean::dec(x_0);
x_458 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_456);
return x_458;
}
else
{
obj* x_459; uint8 x_461; 
x_459 = lean::cnstr_get(x_456, 0);
lean::inc(x_459);
x_461 = lean::cnstr_get_scalar<uint8>(x_456, sizeof(void*)*1);
x_76 = x_456;
x_77 = x_459;
x_78 = x_461;
goto lbl_79;
}
}
else
{
obj* x_463; uint8 x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
lean::dec(x_80);
x_463 = lean::cnstr_get(x_443, 0);
x_465 = lean::cnstr_get_scalar<uint8>(x_443, sizeof(void*)*1);
if (lean::is_exclusive(x_443)) {
 x_466 = x_443;
} else {
 lean::inc(x_463);
 lean::dec(x_443);
 x_466 = lean::box(0);
}
if (lean::is_scalar(x_466)) {
 x_467 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_467 = x_466;
}
lean::cnstr_set(x_467, 0, x_463);
lean::cnstr_set_scalar(x_467, sizeof(void*)*1, x_465);
x_468 = x_467;
x_469 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_468);
if (lean::obj_tag(x_469) == 0)
{
obj* x_471; 
lean::dec(x_0);
x_471 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_73, x_469);
return x_471;
}
else
{
obj* x_472; uint8 x_474; 
x_472 = lean::cnstr_get(x_469, 0);
lean::inc(x_472);
x_474 = lean::cnstr_get_scalar<uint8>(x_469, sizeof(void*)*1);
x_76 = x_469;
x_77 = x_472;
x_78 = x_474;
goto lbl_79;
}
}
}
lbl_87:
{
obj* x_475; 
x_475 = l_lean_ir_parse__uint16(x_85);
if (lean::obj_tag(x_475) == 0)
{
obj* x_476; obj* x_478; obj* x_480; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_476 = lean::cnstr_get(x_475, 0);
x_478 = lean::cnstr_get(x_475, 1);
x_480 = lean::cnstr_get(x_475, 2);
if (lean::is_exclusive(x_475)) {
 x_482 = x_475;
} else {
 lean::inc(x_476);
 lean::inc(x_478);
 lean::inc(x_480);
 lean::dec(x_475);
 x_482 = lean::box(0);
}
x_483 = lean::apply_1(x_84, x_476);
x_484 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_482)) {
 x_485 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_485 = x_482;
}
lean::cnstr_set(x_485, 0, x_483);
lean::cnstr_set(x_485, 1, x_478);
lean::cnstr_set(x_485, 2, x_484);
x_486 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_480, x_485);
x_487 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_486);
if (lean::obj_tag(x_487) == 0)
{
obj* x_488; obj* x_490; obj* x_492; 
x_488 = lean::cnstr_get(x_487, 0);
lean::inc(x_488);
x_490 = lean::cnstr_get(x_487, 1);
lean::inc(x_490);
x_492 = lean::cnstr_get(x_487, 2);
lean::inc(x_492);
lean::dec(x_487);
x_80 = x_488;
x_81 = x_490;
x_82 = x_492;
goto lbl_83;
}
else
{
obj* x_495; uint8 x_497; obj* x_498; obj* x_500; obj* x_501; 
x_495 = lean::cnstr_get(x_487, 0);
x_497 = lean::cnstr_get_scalar<uint8>(x_487, sizeof(void*)*1);
if (lean::is_exclusive(x_487)) {
 x_498 = x_487;
} else {
 lean::inc(x_495);
 lean::dec(x_487);
 x_498 = lean::box(0);
}
lean::inc(x_495);
if (lean::is_scalar(x_498)) {
 x_500 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_500 = x_498;
}
lean::cnstr_set(x_500, 0, x_495);
lean::cnstr_set_scalar(x_500, sizeof(void*)*1, x_497);
x_501 = x_500;
x_76 = x_501;
x_77 = x_495;
x_78 = x_497;
goto lbl_79;
}
}
else
{
obj* x_503; uint8 x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; 
lean::dec(x_84);
x_503 = lean::cnstr_get(x_475, 0);
x_505 = lean::cnstr_get_scalar<uint8>(x_475, sizeof(void*)*1);
if (lean::is_exclusive(x_475)) {
 x_506 = x_475;
} else {
 lean::inc(x_503);
 lean::dec(x_475);
 x_506 = lean::box(0);
}
if (lean::is_scalar(x_506)) {
 x_507 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_507 = x_506;
}
lean::cnstr_set(x_507, 0, x_503);
lean::cnstr_set_scalar(x_507, sizeof(void*)*1, x_505);
x_508 = x_507;
x_509 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_508);
if (lean::obj_tag(x_509) == 0)
{
obj* x_510; obj* x_512; obj* x_514; 
x_510 = lean::cnstr_get(x_509, 0);
lean::inc(x_510);
x_512 = lean::cnstr_get(x_509, 1);
lean::inc(x_512);
x_514 = lean::cnstr_get(x_509, 2);
lean::inc(x_514);
lean::dec(x_509);
x_80 = x_510;
x_81 = x_512;
x_82 = x_514;
goto lbl_83;
}
else
{
obj* x_517; uint8 x_519; obj* x_520; obj* x_522; obj* x_523; 
x_517 = lean::cnstr_get(x_509, 0);
x_519 = lean::cnstr_get_scalar<uint8>(x_509, sizeof(void*)*1);
if (lean::is_exclusive(x_509)) {
 x_520 = x_509;
} else {
 lean::inc(x_517);
 lean::dec(x_509);
 x_520 = lean::box(0);
}
lean::inc(x_517);
if (lean::is_scalar(x_520)) {
 x_522 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_522 = x_520;
}
lean::cnstr_set(x_522, 0, x_517);
lean::cnstr_set_scalar(x_522, sizeof(void*)*1, x_519);
x_523 = x_522;
x_76 = x_523;
x_77 = x_517;
x_78 = x_519;
goto lbl_79;
}
}
}
}
}
lbl_6:
{
obj* x_524; 
x_524 = l_lean_ir_parse__var(x_4);
lean::dec(x_4);
if (lean::obj_tag(x_524) == 0)
{
obj* x_526; obj* x_528; obj* x_530; obj* x_532; obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; 
x_526 = lean::cnstr_get(x_524, 0);
x_528 = lean::cnstr_get(x_524, 1);
x_530 = lean::cnstr_get(x_524, 2);
if (lean::is_exclusive(x_524)) {
 x_532 = x_524;
} else {
 lean::inc(x_526);
 lean::inc(x_528);
 lean::inc(x_530);
 lean::dec(x_524);
 x_532 = lean::box(0);
}
x_533 = lean::apply_1(x_3, x_526);
x_534 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_532)) {
 x_535 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_535 = x_532;
}
lean::cnstr_set(x_535, 0, x_533);
lean::cnstr_set(x_535, 1, x_528);
lean::cnstr_set(x_535, 2, x_534);
x_536 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_530, x_535);
x_537 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_536);
x_1 = x_537;
goto lbl_2;
}
else
{
obj* x_539; uint8 x_541; obj* x_542; obj* x_543; obj* x_544; obj* x_545; 
lean::dec(x_3);
x_539 = lean::cnstr_get(x_524, 0);
x_541 = lean::cnstr_get_scalar<uint8>(x_524, sizeof(void*)*1);
if (lean::is_exclusive(x_524)) {
 x_542 = x_524;
} else {
 lean::inc(x_539);
 lean::dec(x_524);
 x_542 = lean::box(0);
}
if (lean::is_scalar(x_542)) {
 x_543 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_543 = x_542;
}
lean::cnstr_set(x_543, 0, x_539);
lean::cnstr_set_scalar(x_543, sizeof(void*)*1, x_541);
x_544 = x_543;
x_545 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_544);
x_1 = x_545;
goto lbl_2;
}
}
lbl_10:
{
obj* x_546; 
x_546 = l_lean_ir_parse__var(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_546) == 0)
{
obj* x_548; obj* x_550; obj* x_552; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; 
x_548 = lean::cnstr_get(x_546, 0);
x_550 = lean::cnstr_get(x_546, 1);
x_552 = lean::cnstr_get(x_546, 2);
if (lean::is_exclusive(x_546)) {
 x_554 = x_546;
} else {
 lean::inc(x_548);
 lean::inc(x_550);
 lean::inc(x_552);
 lean::dec(x_546);
 x_554 = lean::box(0);
}
x_555 = lean::apply_1(x_7, x_548);
x_556 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_554)) {
 x_557 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_557 = x_554;
}
lean::cnstr_set(x_557, 0, x_555);
lean::cnstr_set(x_557, 1, x_550);
lean::cnstr_set(x_557, 2, x_556);
x_558 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_552, x_557);
x_559 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_558);
if (lean::obj_tag(x_559) == 0)
{
obj* x_560; obj* x_562; obj* x_564; 
x_560 = lean::cnstr_get(x_559, 0);
lean::inc(x_560);
x_562 = lean::cnstr_get(x_559, 1);
lean::inc(x_562);
x_564 = lean::cnstr_get(x_559, 2);
lean::inc(x_564);
lean::dec(x_559);
x_3 = x_560;
x_4 = x_562;
x_5 = x_564;
goto lbl_6;
}
else
{
obj* x_567; uint8 x_569; obj* x_570; obj* x_571; obj* x_572; 
x_567 = lean::cnstr_get(x_559, 0);
x_569 = lean::cnstr_get_scalar<uint8>(x_559, sizeof(void*)*1);
if (lean::is_exclusive(x_559)) {
 x_570 = x_559;
} else {
 lean::inc(x_567);
 lean::dec(x_559);
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
x_1 = x_572;
goto lbl_2;
}
}
else
{
obj* x_574; uint8 x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; 
lean::dec(x_7);
x_574 = lean::cnstr_get(x_546, 0);
x_576 = lean::cnstr_get_scalar<uint8>(x_546, sizeof(void*)*1);
if (lean::is_exclusive(x_546)) {
 x_577 = x_546;
} else {
 lean::inc(x_574);
 lean::dec(x_546);
 x_577 = lean::box(0);
}
if (lean::is_scalar(x_577)) {
 x_578 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_578 = x_577;
}
lean::cnstr_set(x_578, 0, x_574);
lean::cnstr_set_scalar(x_578, sizeof(void*)*1, x_576);
x_579 = x_578;
x_580 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_579);
if (lean::obj_tag(x_580) == 0)
{
obj* x_581; obj* x_583; obj* x_585; 
x_581 = lean::cnstr_get(x_580, 0);
lean::inc(x_581);
x_583 = lean::cnstr_get(x_580, 1);
lean::inc(x_583);
x_585 = lean::cnstr_get(x_580, 2);
lean::inc(x_585);
lean::dec(x_580);
x_3 = x_581;
x_4 = x_583;
x_5 = x_585;
goto lbl_6;
}
else
{
obj* x_588; uint8 x_590; obj* x_591; obj* x_592; obj* x_593; 
x_588 = lean::cnstr_get(x_580, 0);
x_590 = lean::cnstr_get_scalar<uint8>(x_580, sizeof(void*)*1);
if (lean::is_exclusive(x_580)) {
 x_591 = x_580;
} else {
 lean::inc(x_588);
 lean::dec(x_580);
 x_591 = lean::box(0);
}
if (lean::is_scalar(x_591)) {
 x_592 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_592 = x_591;
}
lean::cnstr_set(x_592, 0, x_588);
lean::cnstr_set_scalar(x_592, sizeof(void*)*1, x_590);
x_593 = x_592;
x_1 = x_593;
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
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_parse__instr___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = l_lean_ir_parse__instr___lambda__2(x_0, x_3, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_parse__instr___lambda__3(x_0, x_3, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_parse__instr___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__instr___lambda__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__phi___spec__2(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__var(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
lean::dec(x_2);
if (lean::obj_tag(x_173) == 0)
{
obj* x_175; obj* x_177; obj* x_179; obj* x_181; obj* x_182; uint8 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_175 = lean::cnstr_get(x_173, 0);
x_177 = lean::cnstr_get(x_173, 1);
x_179 = lean::cnstr_get(x_173, 2);
if (lean::is_exclusive(x_173)) {
 x_181 = x_173;
} else {
 lean::inc(x_175);
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_173);
 x_181 = lean::box(0);
}
x_182 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_182, 0, x_168);
lean::cnstr_set(x_182, 1, x_175);
x_183 = lean::unbox(x_170);
lean::cnstr_set_scalar(x_182, sizeof(void*)*2, x_183);
x_184 = x_182;
x_185 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_181)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_181;
}
lean::cnstr_set(x_186, 0, x_184);
lean::cnstr_set(x_186, 1, x_177);
lean::cnstr_set(x_186, 2, x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_179, x_186);
x_188 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_187);
return x_188;
}
else
{
obj* x_191; uint8 x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
lean::dec(x_170);
lean::dec(x_168);
x_191 = lean::cnstr_get(x_173, 0);
x_193 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
if (lean::is_exclusive(x_173)) {
 x_194 = x_173;
} else {
 lean::inc(x_191);
 lean::dec(x_173);
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
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_196);
return x_197;
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
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__phi___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__phi___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__phi(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_12; obj* x_14; obj* x_17; obj* x_19; 
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 2);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_lean_ir_parse__blockid(x_12);
lean::dec(x_12);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_17);
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
x_6 = x_20;
x_7 = x_22;
x_8 = x_24;
goto lbl_9;
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
x_35 = lean::cnstr_get(x_11, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_38 = x_11;
} else {
 lean::inc(x_35);
 lean::dec(x_11);
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
lbl_9:
{
obj* x_42; obj* x_44; 
lean::inc(x_7);
x_42 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_5, x_7);
lean::dec(x_5);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; 
lean::dec(x_7);
x_47 = lean::box(0);
x_44 = x_47;
goto lbl_45;
}
else
{
obj* x_48; uint8 x_50; 
x_48 = lean::cnstr_get(x_42, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_52; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_42);
x_52 = lean::box(0);
x_53 = lean::cnstr_get(x_48, 2);
lean::inc(x_53);
lean::dec(x_48);
x_56 = l_mjoin___rarg___closed__1;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_57, 0, x_53);
lean::closure_set(x_57, 1, x_56);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_6);
lean::cnstr_set(x_58, 1, x_52);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_59, 0, x_57);
lean::closure_set(x_59, 1, x_56);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_7);
lean::cnstr_set(x_61, 2, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_61);
return x_62;
}
else
{
obj* x_65; 
lean::dec(x_7);
lean::dec(x_48);
x_65 = lean::box(0);
x_44 = x_65;
goto lbl_45;
}
}
lbl_45:
{
lean::dec(x_44);
if (lean::obj_tag(x_42) == 0)
{
obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_67 = lean::cnstr_get(x_42, 0);
x_69 = lean::cnstr_get(x_42, 1);
x_71 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 x_73 = x_42;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_42);
 x_73 = lean::box(0);
}
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_6);
lean::cnstr_set(x_74, 1, x_67);
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_77);
return x_78;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_6);
x_80 = lean::cnstr_get(x_42, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_83 = x_42;
} else {
 lean::inc(x_80);
 lean::dec(x_42);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_85);
return x_86;
}
}
}
}
else
{
obj* x_87; obj* x_88; 
x_87 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___closed__1;
x_88 = l_lean_ir_symbol(x_87, x_1);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_94; obj* x_96; 
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_94 = l_lean_ir_parse__blockid(x_89);
lean::dec(x_89);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_94);
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
x_104 = lean::box(0);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_97);
lean::cnstr_set(x_105, 1, x_104);
x_106 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_103)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_103;
}
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_99);
lean::cnstr_set(x_107, 2, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_107);
return x_108;
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; 
x_109 = lean::cnstr_get(x_96, 0);
x_111 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (lean::is_exclusive(x_96)) {
 x_112 = x_96;
} else {
 lean::inc(x_109);
 lean::dec(x_96);
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_sep__by1___rarg___lambda__1___boxed), 2, 1);
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
obj* x_4; 
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
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
lean::dec(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
x_17 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_13);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_23);
x_1 = x_24;
goto lbl_2;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
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
obj* x_47; obj* x_49; 
lean::dec(x_1);
x_47 = l_lean_ir_parse__terminator___closed__2;
lean::inc(x_0);
x_49 = l_lean_ir_keyword(x_47, x_0);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_55; 
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 2);
lean::inc(x_52);
lean::dec(x_49);
x_55 = l_lean_ir_parse__var(x_50);
lean::dec(x_50);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_57 = lean::cnstr_get(x_55, 0);
x_59 = lean::cnstr_get(x_55, 1);
x_61 = lean::cnstr_get(x_55, 2);
if (lean::is_exclusive(x_55)) {
 x_63 = x_55;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_55);
 x_63 = lean::box(0);
}
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_57);
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_63)) {
 x_66 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_66 = x_63;
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
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_74 = lean::cnstr_get(x_55, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
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
obj* x_102; obj* x_104; obj* x_107; 
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 2);
lean::inc(x_104);
lean::dec(x_101);
x_107 = l_lean_ir_parse__var(x_102);
lean::dec(x_102);
if (lean::obj_tag(x_107) == 0)
{
obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_109 = lean::cnstr_get(x_107, 0);
x_111 = lean::cnstr_get(x_107, 1);
x_113 = lean::cnstr_get(x_107, 2);
if (lean::is_exclusive(x_107)) {
 x_115 = x_107;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_107);
 x_115 = lean::box(0);
}
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__terminator___lambda__1___boxed), 2, 1);
lean::closure_set(x_116, 0, x_109);
x_117 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_115)) {
 x_118 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_118 = x_115;
}
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_111);
lean::cnstr_set(x_118, 2, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_118);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_104, x_119);
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
x_95 = x_121;
x_96 = x_123;
x_97 = x_125;
goto lbl_98;
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
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_107, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_107, sizeof(void*)*1);
if (lean::is_exclusive(x_107)) {
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
lean::dec(x_43);
lean::dec(x_0);
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
obj* x_175; obj* x_177; obj* x_180; obj* x_182; 
x_175 = lean::cnstr_get(x_174, 1);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 2);
lean::inc(x_177);
lean::dec(x_174);
x_180 = l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(x_175);
lean::dec(x_175);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_177, x_180);
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
x_169 = x_183;
x_170 = x_185;
x_171 = x_187;
goto lbl_172;
}
else
{
obj* x_191; uint8 x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_95);
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
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_196);
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_198);
return x_199;
}
}
else
{
obj* x_201; uint8 x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_95);
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
x_207 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_206);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_207);
x_209 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_208);
return x_209;
}
lbl_172:
{
obj* x_210; obj* x_211; 
x_210 = l_list_repr___main___rarg___closed__3;
x_211 = l_lean_ir_symbol(x_210, x_170);
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
lean::cnstr_set(x_218, 0, x_169);
lean::cnstr_set(x_218, 1, x_212);
lean::cnstr_set(x_218, 2, x_217);
x_219 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_218);
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_219);
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
x_228 = lean::apply_1(x_95, x_221);
if (lean::is_scalar(x_227)) {
 x_229 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_229 = x_227;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_223);
lean::cnstr_set(x_229, 2, x_217);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_225, x_229);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_231);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_232);
return x_233;
}
else
{
obj* x_235; uint8 x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
lean::dec(x_95);
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
x_241 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_240);
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_241);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_242);
return x_243;
}
}
else
{
obj* x_245; uint8 x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_169);
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
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_171, x_250);
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
x_259 = lean::apply_1(x_95, x_252);
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
x_263 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_262);
x_264 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_43, x_263);
x_265 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_264);
return x_265;
}
else
{
obj* x_267; uint8 x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_95);
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
x_273 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_97, x_272);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__terminator___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_sep__by1___at_lean_ir_parse__terminator___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__terminator___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_parse__terminator___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
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
obj* x_72; obj* x_74; 
x_72 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3(x_5, x_7);
lean::dec(x_5);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; 
lean::dec(x_7);
x_77 = lean::box(0);
x_74 = x_77;
goto lbl_75;
}
else
{
obj* x_78; uint8 x_80; 
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
if (x_80 == 0)
{
obj* x_82; obj* x_83; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_72);
x_82 = lean::box(0);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_86 = l_mjoin___rarg___closed__1;
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_87, 0, x_83);
lean::closure_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_6);
lean::cnstr_set(x_88, 1, x_82);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_89, 0, x_87);
lean::closure_set(x_89, 1, x_86);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_7);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_91);
return x_92;
}
else
{
obj* x_95; 
lean::dec(x_78);
lean::dec(x_7);
x_95 = lean::box(0);
x_74 = x_95;
goto lbl_75;
}
}
lbl_75:
{
lean::dec(x_74);
if (lean::obj_tag(x_72) == 0)
{
obj* x_97; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_97 = lean::cnstr_get(x_72, 0);
x_99 = lean::cnstr_get(x_72, 1);
x_101 = lean::cnstr_get(x_72, 2);
if (lean::is_exclusive(x_72)) {
 x_103 = x_72;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::inc(x_101);
 lean::dec(x_72);
 x_103 = lean::box(0);
}
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_6);
lean::cnstr_set(x_104, 1, x_97);
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
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_107);
return x_108;
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_6);
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
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_115);
return x_116;
}
}
}
}
else
{
obj* x_117; 
x_117 = l_lean_ir_parse__phi(x_1);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_120; obj* x_122; obj* x_125; obj* x_126; 
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_117, 2);
lean::inc(x_122);
lean::dec(x_117);
x_125 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__block___spec__3___closed__1;
x_126 = l_lean_ir_symbol(x_125, x_120);
if (lean::obj_tag(x_126) == 0)
{
obj* x_127; obj* x_129; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_127 = lean::cnstr_get(x_126, 1);
x_129 = lean::cnstr_get(x_126, 2);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_131 = x_126;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_126);
 x_131 = lean::box(0);
}
x_132 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_118);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_132);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_136 = lean::cnstr_get(x_135, 0);
x_138 = lean::cnstr_get(x_135, 1);
x_140 = lean::cnstr_get(x_135, 2);
if (lean::is_exclusive(x_135)) {
 x_142 = x_135;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::inc(x_140);
 lean::dec(x_135);
 x_142 = lean::box(0);
}
x_143 = lean::box(0);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_136);
lean::cnstr_set(x_144, 1, x_143);
if (lean::is_scalar(x_142)) {
 x_145 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_145 = x_142;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_138);
lean::cnstr_set(x_145, 2, x_132);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_140, x_145);
return x_146;
}
else
{
obj* x_147; uint8 x_149; obj* x_150; obj* x_151; obj* x_152; 
x_147 = lean::cnstr_get(x_135, 0);
x_149 = lean::cnstr_get_scalar<uint8>(x_135, sizeof(void*)*1);
if (lean::is_exclusive(x_135)) {
 x_150 = x_135;
} else {
 lean::inc(x_147);
 lean::dec(x_135);
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
return x_152;
}
}
else
{
obj* x_154; uint8 x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_118);
x_154 = lean::cnstr_get(x_126, 0);
x_156 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
if (lean::is_exclusive(x_126)) {
 x_157 = x_126;
} else {
 lean::inc(x_154);
 lean::dec(x_126);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_154);
lean::cnstr_set_scalar(x_158, sizeof(void*)*1, x_156);
x_159 = x_158;
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_161 = lean::cnstr_get(x_160, 0);
x_163 = lean::cnstr_get(x_160, 1);
x_165 = lean::cnstr_get(x_160, 2);
if (lean::is_exclusive(x_160)) {
 x_167 = x_160;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::inc(x_165);
 lean::dec(x_160);
 x_167 = lean::box(0);
}
x_168 = lean::box(0);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_161);
lean::cnstr_set(x_169, 1, x_168);
x_170 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_167)) {
 x_171 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_171 = x_167;
}
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set(x_171, 1, x_163);
lean::cnstr_set(x_171, 2, x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_165, x_171);
return x_172;
}
else
{
obj* x_173; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; 
x_173 = lean::cnstr_get(x_160, 0);
x_175 = lean::cnstr_get_scalar<uint8>(x_160, sizeof(void*)*1);
if (lean::is_exclusive(x_160)) {
 x_176 = x_160;
} else {
 lean::inc(x_173);
 lean::dec(x_160);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_175);
x_178 = x_177;
return x_178;
}
}
}
else
{
obj* x_179; uint8 x_181; obj* x_182; obj* x_183; obj* x_184; 
x_179 = lean::cnstr_get(x_117, 0);
x_181 = lean::cnstr_get_scalar<uint8>(x_117, sizeof(void*)*1);
if (lean::is_exclusive(x_117)) {
 x_182 = x_117;
} else {
 lean::inc(x_179);
 lean::dec(x_117);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_179);
lean::cnstr_set_scalar(x_183, sizeof(void*)*1, x_181);
x_184 = x_183;
return x_184;
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
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_mjoin___rarg___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_0);
lean::cnstr_set(x_14, 2, x_12);
return x_14;
}
else
{
lean::dec(x_2);
return x_1;
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
lean::dec(x_2);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_75; 
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_66, 2);
lean::inc(x_72);
lean::dec(x_66);
x_75 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__4(x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_83; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
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
obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_93 = lean::cnstr_get(x_92, 1);
x_95 = lean::cnstr_get(x_92, 2);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_97 = x_92;
} else {
 lean::inc(x_93);
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
x_98 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_97)) {
 x_99 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_99 = x_97;
}
lean::cnstr_set(x_99, 0, x_84);
lean::cnstr_set(x_99, 1, x_93);
lean::cnstr_set(x_99, 2, x_98);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_102 = lean::cnstr_get(x_101, 0);
x_104 = lean::cnstr_get(x_101, 1);
x_106 = lean::cnstr_get(x_101, 2);
if (lean::is_exclusive(x_101)) {
 x_108 = x_101;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_101);
 x_108 = lean::box(0);
}
x_109 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_109, 0, x_1);
lean::cnstr_set(x_109, 1, x_68);
lean::cnstr_set(x_109, 2, x_76);
lean::cnstr_set(x_109, 3, x_102);
if (lean::is_scalar(x_108)) {
 x_110 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_110 = x_108;
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
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_68);
x_118 = lean::cnstr_get(x_101, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_exclusive(x_101)) {
 x_121 = x_101;
} else {
 lean::inc(x_118);
 lean::dec(x_101);
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
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_123);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_124);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_125);
return x_126;
}
}
else
{
obj* x_128; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_84);
x_128 = lean::cnstr_get(x_92, 0);
x_130 = lean::cnstr_get_scalar<uint8>(x_92, sizeof(void*)*1);
if (lean::is_exclusive(x_92)) {
 x_131 = x_92;
} else {
 lean::inc(x_128);
 lean::dec(x_92);
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
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_133);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_135 = lean::cnstr_get(x_134, 0);
x_137 = lean::cnstr_get(x_134, 1);
x_139 = lean::cnstr_get(x_134, 2);
if (lean::is_exclusive(x_134)) {
 x_141 = x_134;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_134);
 x_141 = lean::box(0);
}
x_142 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_142, 0, x_1);
lean::cnstr_set(x_142, 1, x_68);
lean::cnstr_set(x_142, 2, x_76);
lean::cnstr_set(x_142, 3, x_135);
x_143 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_141)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_141;
}
lean::cnstr_set(x_144, 0, x_142);
lean::cnstr_set(x_144, 1, x_137);
lean::cnstr_set(x_144, 2, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_139, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_146);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_147);
return x_148;
}
else
{
obj* x_152; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_68);
x_152 = lean::cnstr_get(x_134, 0);
x_154 = lean::cnstr_get_scalar<uint8>(x_134, sizeof(void*)*1);
if (lean::is_exclusive(x_134)) {
 x_155 = x_134;
} else {
 lean::inc(x_152);
 lean::dec(x_134);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_152);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = x_156;
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_157);
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_158);
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_159);
return x_160;
}
}
}
else
{
obj* x_164; uint8 x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_76);
lean::dec(x_1);
lean::dec(x_68);
x_164 = lean::cnstr_get(x_83, 0);
x_166 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 x_167 = x_83;
} else {
 lean::inc(x_164);
 lean::dec(x_83);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_164);
lean::cnstr_set_scalar(x_168, sizeof(void*)*1, x_166);
x_169 = x_168;
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_169);
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_171);
return x_172;
}
}
else
{
obj* x_175; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_1);
lean::dec(x_68);
x_175 = lean::cnstr_get(x_75, 0);
x_177 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 x_178 = x_75;
} else {
 lean::inc(x_175);
 lean::dec(x_75);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_175);
lean::cnstr_set_scalar(x_179, sizeof(void*)*1, x_177);
x_180 = x_179;
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_180);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_181);
return x_182;
}
}
else
{
obj* x_184; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
lean::dec(x_1);
x_184 = lean::cnstr_get(x_66, 0);
x_186 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 x_187 = x_66;
} else {
 lean::inc(x_184);
 lean::dec(x_66);
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
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_189);
return x_190;
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
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__block___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__block___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_ir_parse__block___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_parse__block(x_0);
lean::dec(x_0);
return x_1;
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
lean::dec(x_3);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_8, 2);
lean::inc(x_14);
lean::dec(x_8);
x_17 = l_lean_ir_parse__typed__assignment___closed__1;
x_18 = l_lean_ir_symbol(x_17, x_12);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 2);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_lean_ir_parse__typed__assignment___closed__2;
x_25 = l_lean_ir_str2type;
x_26 = l_lean_ir_parse__key2val___main___rarg(x_24, x_25, x_19);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 2);
lean::inc(x_31);
lean::dec(x_26);
x_34 = l_option_has__repr___rarg___closed__3;
x_35 = l_lean_ir_symbol(x_34, x_29);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_38; obj* x_40; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_36 = lean::cnstr_get(x_35, 1);
x_38 = lean::cnstr_get(x_35, 2);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_40 = x_35;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::dec(x_35);
 x_40 = lean::box(0);
}
x_41 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_41, 0, x_10);
x_42 = lean::unbox(x_27);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_42);
x_43 = x_41;
x_44 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_36);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_38, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_48);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_49);
return x_50;
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_10);
lean::dec(x_27);
x_53 = lean::cnstr_get(x_35, 0);
x_55 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 x_56 = x_35;
} else {
 lean::inc(x_53);
 lean::dec(x_35);
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
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_61);
return x_62;
}
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_10);
x_64 = lean::cnstr_get(x_26, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_67 = x_26;
} else {
 lean::inc(x_64);
 lean::dec(x_26);
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
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_70);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_71);
return x_72;
}
}
else
{
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_10);
x_74 = lean::cnstr_get(x_18, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_77 = x_18;
} else {
 lean::inc(x_74);
 lean::dec(x_18);
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
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_80);
return x_81;
}
}
else
{
obj* x_82; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_82 = lean::cnstr_get(x_8, 0);
x_84 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_85 = x_8;
} else {
 lean::inc(x_82);
 lean::dec(x_8);
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
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_87);
return x_88;
}
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; 
x_89 = lean::cnstr_get(x_2, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_92 = x_2;
} else {
 lean::inc(x_89);
 lean::dec(x_2);
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
return x_94;
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
lean::dec(x_1);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_mjoin___rarg___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_0);
lean::cnstr_set(x_14, 2, x_12);
return x_14;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
}
obj* l_lean_ir_parse__def___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
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
lean::dec(x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_13, 1);
x_19 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1___boxed), 2, 1);
lean::closure_set(x_22, 0, x_15);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_29; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 2);
lean::inc(x_31);
lean::dec(x_26);
x_1 = x_27;
x_2 = x_29;
x_3 = x_31;
goto lbl_4;
}
else
{
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_26, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_37 = x_26;
} else {
 lean::inc(x_34);
 lean::dec(x_26);
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
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
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
obj* x_68; obj* x_70; obj* x_73; obj* x_75; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(x_68);
lean::dec(x_68);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_73);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_75, 0);
x_78 = lean::cnstr_get(x_75, 1);
x_80 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = lean::apply_1(x_1, x_76);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_82)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_82;
}
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_78);
lean::cnstr_set(x_85, 2, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_85);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_86);
return x_87;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_1);
x_89 = lean::cnstr_get(x_75, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 x_92 = x_75;
} else {
 lean::inc(x_89);
 lean::dec(x_75);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__def___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__def___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__def___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__def___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_parse__def___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_14 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_13, x_7);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_11);
lean::dec(x_7);
x_20 = lean::box(0);
x_16 = x_20;
goto lbl_17;
}
else
{
obj* x_21; uint8 x_23; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_25 = lean::box(0);
x_26 = lean::cnstr_get(x_21, 2);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_mjoin___rarg___closed__1;
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_30, 0, x_26);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_25);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_7);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_34);
return x_35;
}
else
{
obj* x_39; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_21);
x_39 = lean::box(0);
x_16 = x_39;
goto lbl_17;
}
}
lbl_17:
{
lean::dec(x_16);
if (lean::obj_tag(x_14) == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
x_45 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_5);
lean::cnstr_set(x_48, 1, x_41);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_47;
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
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_5);
x_54 = lean::cnstr_get(x_14, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_57 = x_14;
} else {
 lean::inc(x_54);
 lean::dec(x_14);
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
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_59);
return x_60;
}
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_64 = x_4;
} else {
 lean::inc(x_61);
 lean::dec(x_4);
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
else
{
obj* x_67; 
x_67 = l_lean_ir_parse__block(x_1);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
x_72 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 x_74 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_67);
 x_74 = lean::box(0);
}
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_68);
lean::cnstr_set(x_76, 1, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_70);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_78);
return x_79;
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_67, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_83 = x_67;
} else {
 lean::inc(x_80);
 lean::dec(x_67);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = x_84;
return x_85;
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
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_mjoin___rarg___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_0);
lean::cnstr_set(x_14, 2, x_12);
return x_14;
}
else
{
lean::dec(x_2);
return x_1;
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
lean::dec(x_7);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_13, 1);
x_19 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__def___lambda__1___boxed), 2, 1);
lean::closure_set(x_22, 0, x_15);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_29; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 2);
lean::inc(x_31);
lean::dec(x_26);
x_1 = x_27;
x_2 = x_29;
x_3 = x_31;
goto lbl_4;
}
else
{
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_26, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_37 = x_26;
} else {
 lean::inc(x_34);
 lean::dec(x_26);
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
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
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
obj* x_68; obj* x_70; obj* x_73; obj* x_75; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(x_68);
lean::dec(x_68);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_73);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_75, 0);
x_78 = lean::cnstr_get(x_75, 1);
x_80 = lean::cnstr_get(x_75, 2);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_75);
 x_82 = lean::box(0);
}
x_83 = lean::apply_1(x_1, x_76);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_82)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_82;
}
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_78);
lean::cnstr_set(x_85, 2, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_85);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_3, x_86);
return x_87;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_1);
x_89 = lean::cnstr_get(x_75, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 x_92 = x_75;
} else {
 lean::inc(x_89);
 lean::dec(x_75);
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
obj* l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_many1__aux___main___at_lean_ir_parse__defconst___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many1___at_lean_ir_parse__defconst___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_many___at_lean_ir_parse__defconst___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
lean::dec(x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_9, 0);
x_13 = lean::cnstr_get(x_9, 1);
x_15 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_11);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_17;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_21);
return x_22;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
