// Lean compiler output
// Module: init.lean.parser.string_literal
// Imports: init.lean.parser.parsec
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7(obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___rarg(obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_labels___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__hex__digit___rarg(obj*, obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10(obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux(obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3(obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6(obj*, obj*, obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__string__literal(obj*, obj*);
obj* l_lean_parser_parse__string__literal___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4(obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_parse__string__literal___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit(obj*, obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___boxed(obj*, obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1(obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__5(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(obj*, obj*, uint32);
extern obj* l_lean_parser_monad__parsec_remaining___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal___rarg___lambda__2(obj*, obj*, obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__quoted__char___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10(obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; uint32 x_9; uint32 x_10; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::uint32_to_nat(x_1);
x_9 = 48;
x_10 = 55296;
x_11 = x_9 < x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 57343;
x_13 = x_12 < x_9;
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; 
x_14 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_15 = lean::nat_sub(x_8, x_14);
lean::dec(x_8);
x_17 = lean::apply_2(x_5, lean::box(0), x_15);
return x_17;
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = 1114112;
x_19 = x_9 < x_18;
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_23; 
x_20 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_21 = lean::nat_sub(x_8, x_20);
lean::dec(x_8);
x_23 = lean::apply_2(x_5, lean::box(0), x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_25 = lean::nat_sub(x_8, x_24);
lean::dec(x_8);
x_27 = lean::apply_2(x_5, lean::box(0), x_25);
return x_27;
}
}
}
else
{
obj* x_28; obj* x_29; obj* x_31; 
x_28 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_29 = lean::nat_sub(x_8, x_28);
lean::dec(x_8);
x_31 = lean::apply_2(x_5, lean::box(0), x_29);
return x_31;
}
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__1___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
uint32 x_15; obj* x_16; uint32 x_18; uint32 x_19; uint8 x_20; uint8 x_21; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = 97;
x_19 = 55296;
x_20 = x_18 < x_19;
if (x_20 == 0)
{
uint32 x_23; uint8 x_24; 
x_23 = 57343;
x_24 = x_23 < x_18;
if (x_24 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 0;
x_26 = x_25 <= x_15;
if (x_26 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_2);
x_29 = lean::box(0);
x_16 = x_29;
goto lbl_17;
}
else
{
uint8 x_30; 
x_30 = 1;
x_21 = x_30;
goto lbl_22;
}
}
else
{
uint32 x_31; uint8 x_32; 
x_31 = 1114112;
x_32 = x_18 < x_31;
if (x_32 == 0)
{
uint32 x_33; uint8 x_34; 
x_33 = 0;
x_34 = x_33 <= x_15;
if (x_34 == 0)
{
obj* x_37; 
lean::dec(x_3);
lean::dec(x_2);
x_37 = lean::box(0);
x_16 = x_37;
goto lbl_17;
}
else
{
uint8 x_38; 
x_38 = 1;
x_21 = x_38;
goto lbl_22;
}
}
else
{
uint8 x_39; 
x_39 = x_18 <= x_15;
if (x_39 == 0)
{
obj* x_42; 
lean::dec(x_3);
lean::dec(x_2);
x_42 = lean::box(0);
x_16 = x_42;
goto lbl_17;
}
else
{
uint8 x_43; 
x_43 = 1;
x_21 = x_43;
goto lbl_22;
}
}
}
}
else
{
uint8 x_44; 
x_44 = x_18 <= x_15;
if (x_44 == 0)
{
obj* x_47; 
lean::dec(x_3);
lean::dec(x_2);
x_47 = lean::box(0);
x_16 = x_47;
goto lbl_17;
}
else
{
uint8 x_48; 
x_48 = 1;
x_21 = x_48;
goto lbl_22;
}
}
lbl_17:
{
obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_60; 
lean::dec(x_16);
x_50 = l_char_quote__core(x_15);
x_51 = l_char_has__repr___closed__1;
lean::inc(x_51);
x_53 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_55 = lean::string_append(x_53, x_51);
x_56 = lean::box(0);
x_57 = l_mjoin___rarg___closed__1;
lean::inc(x_56);
lean::inc(x_57);
x_60 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2___rarg(x_1, lean::box(0), x_55, x_57, x_56, x_56);
return x_60;
}
lbl_22:
{
uint32 x_61; uint8 x_62; 
x_61 = 102;
x_62 = x_61 < x_19;
if (x_62 == 0)
{
uint32 x_63; uint8 x_64; 
x_63 = 57343;
x_64 = x_63 < x_61;
if (x_64 == 0)
{
uint32 x_65; uint8 x_66; 
x_65 = 0;
x_66 = x_15 <= x_65;
if (x_66 == 0)
{
obj* x_69; 
lean::dec(x_3);
lean::dec(x_2);
x_69 = lean::box(0);
x_16 = x_69;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_72; 
lean::dec(x_3);
lean::dec(x_2);
x_72 = lean::box(0);
x_16 = x_72;
goto lbl_17;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_74 = lean::box_uint32(x_15);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_75, 0, x_3);
lean::closure_set(x_75, 1, x_74);
x_76 = lean::apply_2(x_2, lean::box(0), x_75);
return x_76;
}
}
}
else
{
uint32 x_77; uint8 x_78; 
x_77 = 1114112;
x_78 = x_61 < x_77;
if (x_78 == 0)
{
uint32 x_79; uint8 x_80; 
x_79 = 0;
x_80 = x_15 <= x_79;
if (x_80 == 0)
{
obj* x_83; 
lean::dec(x_3);
lean::dec(x_2);
x_83 = lean::box(0);
x_16 = x_83;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_86; 
lean::dec(x_3);
lean::dec(x_2);
x_86 = lean::box(0);
x_16 = x_86;
goto lbl_17;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
x_88 = lean::box_uint32(x_15);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_89, 0, x_3);
lean::closure_set(x_89, 1, x_88);
x_90 = lean::apply_2(x_2, lean::box(0), x_89);
return x_90;
}
}
}
else
{
uint8 x_91; 
x_91 = x_15 <= x_61;
if (x_91 == 0)
{
obj* x_94; 
lean::dec(x_3);
lean::dec(x_2);
x_94 = lean::box(0);
x_16 = x_94;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_97; 
lean::dec(x_3);
lean::dec(x_2);
x_97 = lean::box(0);
x_16 = x_97;
goto lbl_17;
}
else
{
obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_1);
x_99 = lean::box_uint32(x_15);
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_100, 0, x_3);
lean::closure_set(x_100, 1, x_99);
x_101 = lean::apply_2(x_2, lean::box(0), x_100);
return x_101;
}
}
}
}
}
else
{
uint8 x_102; 
x_102 = x_15 <= x_61;
if (x_102 == 0)
{
obj* x_105; 
lean::dec(x_3);
lean::dec(x_2);
x_105 = lean::box(0);
x_16 = x_105;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_108; 
lean::dec(x_3);
lean::dec(x_2);
x_108 = lean::box(0);
x_16 = x_108;
goto lbl_17;
}
else
{
obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_1);
x_110 = lean::box_uint32(x_15);
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_111, 0, x_3);
lean::closure_set(x_111, 1, x_110);
x_112 = lean::apply_2(x_2, lean::box(0), x_111);
return x_112;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 97;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; uint32 x_9; uint32 x_10; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::uint32_to_nat(x_1);
x_9 = 97;
x_10 = 55296;
x_11 = x_9 < x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 57343;
x_13 = x_12 < x_9;
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
x_14 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_15 = lean::nat_sub(x_8, x_14);
lean::dec(x_8);
x_17 = lean::mk_nat_obj(10u);
x_18 = lean::nat_add(x_17, x_15);
lean::dec(x_15);
lean::dec(x_17);
x_21 = lean::apply_2(x_5, lean::box(0), x_18);
return x_21;
}
else
{
uint32 x_22; uint8 x_23; 
x_22 = 1114112;
x_23 = x_9 < x_22;
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_31; 
x_24 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_25 = lean::nat_sub(x_8, x_24);
lean::dec(x_8);
x_27 = lean::mk_nat_obj(10u);
x_28 = lean::nat_add(x_27, x_25);
lean::dec(x_25);
lean::dec(x_27);
x_31 = lean::apply_2(x_5, lean::box(0), x_28);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_39; 
x_32 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_33 = lean::nat_sub(x_8, x_32);
lean::dec(x_8);
x_35 = lean::mk_nat_obj(10u);
x_36 = lean::nat_add(x_35, x_33);
lean::dec(x_33);
lean::dec(x_35);
x_39 = lean::apply_2(x_5, lean::box(0), x_36);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_47; 
x_40 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_41 = lean::nat_sub(x_8, x_40);
lean::dec(x_8);
x_43 = lean::mk_nat_obj(10u);
x_44 = lean::nat_add(x_43, x_41);
lean::dec(x_41);
lean::dec(x_43);
x_47 = lean::apply_2(x_5, lean::box(0), x_44);
return x_47;
}
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__3___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
uint32 x_15; obj* x_16; uint32 x_18; uint32 x_19; uint8 x_20; uint8 x_21; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = 65;
x_19 = 55296;
x_20 = x_18 < x_19;
if (x_20 == 0)
{
uint32 x_23; uint8 x_24; 
x_23 = 57343;
x_24 = x_23 < x_18;
if (x_24 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 0;
x_26 = x_25 <= x_15;
if (x_26 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_2);
x_29 = lean::box(0);
x_16 = x_29;
goto lbl_17;
}
else
{
uint8 x_30; 
x_30 = 1;
x_21 = x_30;
goto lbl_22;
}
}
else
{
uint32 x_31; uint8 x_32; 
x_31 = 1114112;
x_32 = x_18 < x_31;
if (x_32 == 0)
{
uint32 x_33; uint8 x_34; 
x_33 = 0;
x_34 = x_33 <= x_15;
if (x_34 == 0)
{
obj* x_37; 
lean::dec(x_3);
lean::dec(x_2);
x_37 = lean::box(0);
x_16 = x_37;
goto lbl_17;
}
else
{
uint8 x_38; 
x_38 = 1;
x_21 = x_38;
goto lbl_22;
}
}
else
{
uint8 x_39; 
x_39 = x_18 <= x_15;
if (x_39 == 0)
{
obj* x_42; 
lean::dec(x_3);
lean::dec(x_2);
x_42 = lean::box(0);
x_16 = x_42;
goto lbl_17;
}
else
{
uint8 x_43; 
x_43 = 1;
x_21 = x_43;
goto lbl_22;
}
}
}
}
else
{
uint8 x_44; 
x_44 = x_18 <= x_15;
if (x_44 == 0)
{
obj* x_47; 
lean::dec(x_3);
lean::dec(x_2);
x_47 = lean::box(0);
x_16 = x_47;
goto lbl_17;
}
else
{
uint8 x_48; 
x_48 = 1;
x_21 = x_48;
goto lbl_22;
}
}
lbl_17:
{
obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_60; 
lean::dec(x_16);
x_50 = l_char_quote__core(x_15);
x_51 = l_char_has__repr___closed__1;
lean::inc(x_51);
x_53 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_55 = lean::string_append(x_53, x_51);
x_56 = lean::box(0);
x_57 = l_mjoin___rarg___closed__1;
lean::inc(x_56);
lean::inc(x_57);
x_60 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4___rarg(x_1, lean::box(0), x_55, x_57, x_56, x_56);
return x_60;
}
lbl_22:
{
uint32 x_61; uint8 x_62; 
x_61 = 70;
x_62 = x_61 < x_19;
if (x_62 == 0)
{
uint32 x_63; uint8 x_64; 
x_63 = 57343;
x_64 = x_63 < x_61;
if (x_64 == 0)
{
uint32 x_65; uint8 x_66; 
x_65 = 0;
x_66 = x_15 <= x_65;
if (x_66 == 0)
{
obj* x_69; 
lean::dec(x_3);
lean::dec(x_2);
x_69 = lean::box(0);
x_16 = x_69;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_72; 
lean::dec(x_3);
lean::dec(x_2);
x_72 = lean::box(0);
x_16 = x_72;
goto lbl_17;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_74 = lean::box_uint32(x_15);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_75, 0, x_3);
lean::closure_set(x_75, 1, x_74);
x_76 = lean::apply_2(x_2, lean::box(0), x_75);
return x_76;
}
}
}
else
{
uint32 x_77; uint8 x_78; 
x_77 = 1114112;
x_78 = x_61 < x_77;
if (x_78 == 0)
{
uint32 x_79; uint8 x_80; 
x_79 = 0;
x_80 = x_15 <= x_79;
if (x_80 == 0)
{
obj* x_83; 
lean::dec(x_3);
lean::dec(x_2);
x_83 = lean::box(0);
x_16 = x_83;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_86; 
lean::dec(x_3);
lean::dec(x_2);
x_86 = lean::box(0);
x_16 = x_86;
goto lbl_17;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
x_88 = lean::box_uint32(x_15);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_89, 0, x_3);
lean::closure_set(x_89, 1, x_88);
x_90 = lean::apply_2(x_2, lean::box(0), x_89);
return x_90;
}
}
}
else
{
uint8 x_91; 
x_91 = x_15 <= x_61;
if (x_91 == 0)
{
obj* x_94; 
lean::dec(x_3);
lean::dec(x_2);
x_94 = lean::box(0);
x_16 = x_94;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_97; 
lean::dec(x_3);
lean::dec(x_2);
x_97 = lean::box(0);
x_16 = x_97;
goto lbl_17;
}
else
{
obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_1);
x_99 = lean::box_uint32(x_15);
x_100 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_100, 0, x_3);
lean::closure_set(x_100, 1, x_99);
x_101 = lean::apply_2(x_2, lean::box(0), x_100);
return x_101;
}
}
}
}
}
else
{
uint8 x_102; 
x_102 = x_15 <= x_61;
if (x_102 == 0)
{
obj* x_105; 
lean::dec(x_3);
lean::dec(x_2);
x_105 = lean::box(0);
x_16 = x_105;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_108; 
lean::dec(x_3);
lean::dec(x_2);
x_108 = lean::box(0);
x_16 = x_108;
goto lbl_17;
}
else
{
obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_1);
x_110 = lean::box_uint32(x_15);
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_111, 0, x_3);
lean::closure_set(x_111, 1, x_110);
x_112 = lean::apply_2(x_2, lean::box(0), x_111);
return x_112;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 65;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; uint32 x_9; uint32 x_10; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::uint32_to_nat(x_1);
x_9 = 65;
x_10 = 55296;
x_11 = x_9 < x_10;
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 57343;
x_13 = x_12 < x_9;
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
x_14 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_15 = lean::nat_sub(x_8, x_14);
lean::dec(x_8);
x_17 = lean::mk_nat_obj(10u);
x_18 = lean::nat_add(x_17, x_15);
lean::dec(x_15);
lean::dec(x_17);
x_21 = lean::apply_2(x_5, lean::box(0), x_18);
return x_21;
}
else
{
uint32 x_22; uint8 x_23; 
x_22 = 1114112;
x_23 = x_9 < x_22;
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_31; 
x_24 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_25 = lean::nat_sub(x_8, x_24);
lean::dec(x_8);
x_27 = lean::mk_nat_obj(10u);
x_28 = lean::nat_add(x_27, x_25);
lean::dec(x_25);
lean::dec(x_27);
x_31 = lean::apply_2(x_5, lean::box(0), x_28);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_39; 
x_32 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_33 = lean::nat_sub(x_8, x_32);
lean::dec(x_8);
x_35 = lean::mk_nat_obj(10u);
x_36 = lean::nat_add(x_35, x_33);
lean::dec(x_33);
lean::dec(x_35);
x_39 = lean::apply_2(x_5, lean::box(0), x_36);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_47; 
x_40 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_41 = lean::nat_sub(x_8, x_40);
lean::dec(x_8);
x_43 = lean::mk_nat_obj(10u);
x_44 = lean::nat_add(x_43, x_41);
lean::dec(x_41);
lean::dec(x_43);
x_47 = lean::apply_2(x_5, lean::box(0), x_44);
return x_47;
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_parse__hex__digit___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_19; obj* x_23; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_45; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_9 = l_lean_parser_monad__parsec_digit___rarg(x_0, x_1);
lean::inc(x_2);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_11, 0, x_2);
lean::inc(x_5);
x_13 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_16 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_16);
lean::inc(x_14);
x_19 = lean::apply_2(x_14, lean::box(0), x_16);
lean::inc(x_14);
lean::inc(x_1);
lean::inc(x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg___lambda__2), 4, 3);
lean::closure_set(x_23, 0, x_0);
lean::closure_set(x_23, 1, x_1);
lean::closure_set(x_23, 2, x_14);
lean::inc(x_19);
lean::inc(x_5);
x_26 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_19, x_23);
lean::inc(x_2);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg___lambda__3___boxed), 2, 1);
lean::closure_set(x_28, 0, x_2);
lean::inc(x_5);
x_30 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_26, x_28);
lean::inc(x_1);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg___lambda__4), 4, 3);
lean::closure_set(x_32, 0, x_0);
lean::closure_set(x_32, 1, x_1);
lean::closure_set(x_32, 2, x_14);
lean::inc(x_5);
x_34 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_19, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg___lambda__5___boxed), 2, 1);
lean::closure_set(x_35, 0, x_2);
x_36 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_34, x_35);
lean::inc(x_3);
x_38 = lean::apply_3(x_3, lean::box(0), x_30, x_36);
x_39 = lean::apply_3(x_3, lean::box(0), x_13, x_38);
x_40 = lean::cnstr_get(x_1, 1);
lean::inc(x_40);
lean::dec(x_1);
x_43 = l_lean_parser_parse__hex__digit___rarg___closed__1;
lean::inc(x_43);
x_45 = lean::apply_3(x_40, lean::box(0), x_43, x_39);
return x_45;
}
}
obj* l_lean_parser_parse__hex__digit(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__hex__digit___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_parse__hex__digit___rarg___lambda__1(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_parse__hex__digit___rarg___lambda__3(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_parse__hex__digit___rarg___lambda__5(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::box(0);
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2___rarg(x_1, lean::box(0), x_3, x_9, x_7, x_8);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::box(0);
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__4___rarg(x_1, lean::box(0), x_3, x_9, x_7, x_8);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::box(0);
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__6___rarg(x_1, lean::box(0), x_3, x_9, x_7, x_8);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::box(0);
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__8___rarg(x_1, lean::box(0), x_3, x_9, x_7, x_8);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_25; uint32 x_28; uint32 x_30; uint8 x_31; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::mk_nat_obj(16u);
x_12 = lean::nat_mul(x_11, x_1);
lean::dec(x_1);
x_14 = lean::nat_add(x_12, x_2);
lean::dec(x_2);
lean::dec(x_12);
x_17 = lean::nat_mul(x_11, x_14);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_3);
lean::dec(x_3);
lean::dec(x_17);
x_22 = lean::nat_mul(x_11, x_19);
lean::dec(x_19);
lean::dec(x_11);
x_25 = lean::nat_add(x_22, x_4);
lean::dec(x_4);
lean::dec(x_22);
x_28 = lean::uint32_of_nat(x_25);
lean::dec(x_25);
x_30 = 55296;
x_31 = x_28 < x_30;
if (x_31 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 57343;
x_33 = x_32 < x_28;
if (x_33 == 0)
{
uint32 x_34; obj* x_35; obj* x_36; 
x_34 = 0;
x_35 = lean::box_uint32(x_34);
x_36 = lean::apply_2(x_8, lean::box(0), x_35);
return x_36;
}
else
{
uint32 x_37; uint8 x_38; 
x_37 = 1114112;
x_38 = x_28 < x_37;
if (x_38 == 0)
{
uint32 x_39; obj* x_40; obj* x_41; 
x_39 = 0;
x_40 = lean::box_uint32(x_39);
x_41 = lean::apply_2(x_8, lean::box(0), x_40);
return x_41;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::box_uint32(x_28);
x_43 = lean::apply_2(x_8, lean::box(0), x_42);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; 
x_44 = lean::box_uint32(x_28);
x_45 = lean::apply_2(x_8, lean::box(0), x_44);
return x_45;
}
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__1), 5, 4);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
lean::closure_set(x_6, 2, x_2);
lean::closure_set(x_6, 3, x_5);
x_7 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__2), 6, 5);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_1);
lean::closure_set(x_7, 2, x_4);
lean::closure_set(x_7, 3, x_2);
lean::closure_set(x_7, 4, x_3);
x_8 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_7);
return x_8;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__3), 5, 4);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_3);
lean::closure_set(x_6, 2, x_1);
lean::closure_set(x_6, 3, x_2);
x_7 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_13; uint32 x_16; uint32 x_18; uint8 x_19; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::mk_nat_obj(16u);
x_10 = lean::nat_mul(x_9, x_1);
lean::dec(x_1);
lean::dec(x_9);
x_13 = lean::nat_add(x_10, x_2);
lean::dec(x_2);
lean::dec(x_10);
x_16 = lean::uint32_of_nat(x_13);
lean::dec(x_13);
x_18 = 55296;
x_19 = x_16 < x_18;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 57343;
x_21 = x_20 < x_16;
if (x_21 == 0)
{
uint32 x_22; obj* x_23; obj* x_24; 
x_22 = 0;
x_23 = lean::box_uint32(x_22);
x_24 = lean::apply_2(x_6, lean::box(0), x_23);
return x_24;
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = 1114112;
x_26 = x_16 < x_25;
if (x_26 == 0)
{
uint32 x_27; obj* x_28; obj* x_29; 
x_27 = 0;
x_28 = lean::box_uint32(x_27);
x_29 = lean::apply_2(x_6, lean::box(0), x_28);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::box_uint32(x_16);
x_31 = lean::apply_2(x_6, lean::box(0), x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::box_uint32(x_16);
x_33 = lean::apply_2(x_6, lean::box(0), x_32);
return x_33;
}
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__5), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_2, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("quoted character");
return x_0;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, uint32 x_10) {
_start:
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; uint32 x_36; uint32 x_37; uint8 x_38; uint32 x_39; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_36 = 92;
x_37 = 55296;
x_38 = x_36 < x_37;
if (x_38 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = 57343;
x_42 = x_41 < x_36;
if (x_42 == 0)
{
uint32 x_43; 
x_43 = 0;
x_39 = x_43;
goto lbl_40;
}
else
{
uint32 x_44; uint8 x_45; 
x_44 = 1114112;
x_45 = x_36 < x_44;
if (x_45 == 0)
{
uint32 x_46; 
x_46 = 0;
x_39 = x_46;
goto lbl_40;
}
else
{
x_39 = x_36;
goto lbl_40;
}
}
}
else
{
x_39 = x_36;
goto lbl_40;
}
lbl_17:
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_16);
lean::inc(x_9);
x_49 = l_lean_parser_parse__hex__digit___rarg(x_0, x_1, x_9);
lean::inc(x_49);
lean::inc(x_6);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__4), 4, 3);
lean::closure_set(x_52, 0, x_9);
lean::closure_set(x_52, 1, x_6);
lean::closure_set(x_52, 2, x_49);
x_53 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_49, x_52);
return x_53;
}
lbl_19:
{
obj* x_56; obj* x_59; obj* x_60; 
lean::dec(x_18);
lean::inc(x_9);
x_56 = l_lean_parser_parse__hex__digit___rarg(x_0, x_1, x_9);
lean::inc(x_56);
lean::inc(x_6);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__6), 4, 3);
lean::closure_set(x_59, 0, x_9);
lean::closure_set(x_59, 1, x_6);
lean::closure_set(x_59, 2, x_56);
x_60 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_56, x_59);
return x_60;
}
lbl_21:
{
obj* x_62; obj* x_65; uint32 x_68; uint32 x_69; uint8 x_70; 
lean::dec(x_20);
x_62 = lean::cnstr_get(x_9, 0);
lean::inc(x_62);
lean::dec(x_9);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = 9;
x_69 = 55296;
x_70 = x_68 < x_69;
if (x_70 == 0)
{
uint32 x_71; uint8 x_72; 
x_71 = 57343;
x_72 = x_71 < x_68;
if (x_72 == 0)
{
uint32 x_73; obj* x_74; obj* x_75; 
x_73 = 0;
x_74 = lean::box_uint32(x_73);
x_75 = lean::apply_2(x_65, lean::box(0), x_74);
return x_75;
}
else
{
uint32 x_76; uint8 x_77; 
x_76 = 1114112;
x_77 = x_68 < x_76;
if (x_77 == 0)
{
uint32 x_78; obj* x_79; obj* x_80; 
x_78 = 0;
x_79 = lean::box_uint32(x_78);
x_80 = lean::apply_2(x_65, lean::box(0), x_79);
return x_80;
}
else
{
obj* x_81; obj* x_82; 
x_81 = lean::box_uint32(x_68);
x_82 = lean::apply_2(x_65, lean::box(0), x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::box_uint32(x_68);
x_84 = lean::apply_2(x_65, lean::box(0), x_83);
return x_84;
}
}
lbl_23:
{
obj* x_86; obj* x_89; uint32 x_92; uint32 x_93; uint8 x_94; 
lean::dec(x_22);
x_86 = lean::cnstr_get(x_9, 0);
lean::inc(x_86);
lean::dec(x_9);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
lean::dec(x_86);
x_92 = 10;
x_93 = 55296;
x_94 = x_92 < x_93;
if (x_94 == 0)
{
uint32 x_95; uint8 x_96; 
x_95 = 57343;
x_96 = x_95 < x_92;
if (x_96 == 0)
{
uint32 x_97; obj* x_98; obj* x_99; 
x_97 = 0;
x_98 = lean::box_uint32(x_97);
x_99 = lean::apply_2(x_89, lean::box(0), x_98);
return x_99;
}
else
{
uint32 x_100; uint8 x_101; 
x_100 = 1114112;
x_101 = x_92 < x_100;
if (x_101 == 0)
{
uint32 x_102; obj* x_103; obj* x_104; 
x_102 = 0;
x_103 = lean::box_uint32(x_102);
x_104 = lean::apply_2(x_89, lean::box(0), x_103);
return x_104;
}
else
{
obj* x_105; obj* x_106; 
x_105 = lean::box_uint32(x_92);
x_106 = lean::apply_2(x_89, lean::box(0), x_105);
return x_106;
}
}
}
else
{
obj* x_107; obj* x_108; 
x_107 = lean::box_uint32(x_92);
x_108 = lean::apply_2(x_89, lean::box(0), x_107);
return x_108;
}
}
lbl_25:
{
uint32 x_110; uint32 x_111; uint8 x_112; 
lean::dec(x_24);
x_110 = 117;
x_111 = 55296;
x_112 = x_110 < x_111;
if (x_112 == 0)
{
uint32 x_113; uint8 x_114; 
x_113 = 57343;
x_114 = x_113 < x_110;
if (x_114 == 0)
{
uint32 x_115; uint8 x_116; 
x_115 = 0;
x_116 = x_10 == x_115;
if (x_116 == 0)
{
obj* x_119; obj* x_121; 
lean::dec(x_9);
lean::dec(x_6);
x_119 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_119);
x_121 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1___rarg(x_0, x_1, lean::box(0), x_119, x_2);
return x_121;
}
else
{
obj* x_123; 
lean::dec(x_2);
x_123 = lean::box(0);
x_16 = x_123;
goto lbl_17;
}
}
else
{
uint32 x_124; uint8 x_125; 
x_124 = 1114112;
x_125 = x_110 < x_124;
if (x_125 == 0)
{
uint32 x_126; uint8 x_127; 
x_126 = 0;
x_127 = x_10 == x_126;
if (x_127 == 0)
{
obj* x_130; obj* x_132; 
lean::dec(x_9);
lean::dec(x_6);
x_130 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_130);
x_132 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg(x_0, x_1, lean::box(0), x_130, x_2);
return x_132;
}
else
{
obj* x_134; 
lean::dec(x_2);
x_134 = lean::box(0);
x_16 = x_134;
goto lbl_17;
}
}
else
{
uint8 x_135; 
x_135 = x_10 == x_110;
if (x_135 == 0)
{
obj* x_138; obj* x_140; 
lean::dec(x_9);
lean::dec(x_6);
x_138 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_138);
x_140 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5___rarg(x_0, x_1, lean::box(0), x_138, x_2);
return x_140;
}
else
{
obj* x_142; 
lean::dec(x_2);
x_142 = lean::box(0);
x_16 = x_142;
goto lbl_17;
}
}
}
}
else
{
uint8 x_143; 
x_143 = x_10 == x_110;
if (x_143 == 0)
{
obj* x_146; obj* x_148; 
lean::dec(x_9);
lean::dec(x_6);
x_146 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_146);
x_148 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7___rarg(x_0, x_1, lean::box(0), x_146, x_2);
return x_148;
}
else
{
obj* x_150; 
lean::dec(x_2);
x_150 = lean::box(0);
x_16 = x_150;
goto lbl_17;
}
}
}
lbl_27:
{
uint32 x_152; uint32 x_153; uint8 x_154; 
lean::dec(x_26);
x_152 = 120;
x_153 = 55296;
x_154 = x_152 < x_153;
if (x_154 == 0)
{
uint32 x_155; uint8 x_156; 
x_155 = 57343;
x_156 = x_155 < x_152;
if (x_156 == 0)
{
uint32 x_157; uint8 x_158; 
x_157 = 0;
x_158 = x_10 == x_157;
if (x_158 == 0)
{
obj* x_159; 
x_159 = lean::box(0);
x_24 = x_159;
goto lbl_25;
}
else
{
obj* x_161; 
lean::dec(x_2);
x_161 = lean::box(0);
x_18 = x_161;
goto lbl_19;
}
}
else
{
uint32 x_162; uint8 x_163; 
x_162 = 1114112;
x_163 = x_152 < x_162;
if (x_163 == 0)
{
uint32 x_164; uint8 x_165; 
x_164 = 0;
x_165 = x_10 == x_164;
if (x_165 == 0)
{
obj* x_166; 
x_166 = lean::box(0);
x_24 = x_166;
goto lbl_25;
}
else
{
obj* x_168; 
lean::dec(x_2);
x_168 = lean::box(0);
x_18 = x_168;
goto lbl_19;
}
}
else
{
uint8 x_169; 
x_169 = x_10 == x_152;
if (x_169 == 0)
{
obj* x_170; 
x_170 = lean::box(0);
x_24 = x_170;
goto lbl_25;
}
else
{
obj* x_172; 
lean::dec(x_2);
x_172 = lean::box(0);
x_18 = x_172;
goto lbl_19;
}
}
}
}
else
{
uint8 x_173; 
x_173 = x_10 == x_152;
if (x_173 == 0)
{
obj* x_174; 
x_174 = lean::box(0);
x_24 = x_174;
goto lbl_25;
}
else
{
obj* x_176; 
lean::dec(x_2);
x_176 = lean::box(0);
x_18 = x_176;
goto lbl_19;
}
}
}
lbl_29:
{
uint32 x_178; uint32 x_179; uint8 x_180; 
lean::dec(x_28);
x_178 = 116;
x_179 = 55296;
x_180 = x_178 < x_179;
if (x_180 == 0)
{
uint32 x_181; uint8 x_182; 
x_181 = 57343;
x_182 = x_181 < x_178;
if (x_182 == 0)
{
uint32 x_183; uint8 x_184; 
x_183 = 0;
x_184 = x_10 == x_183;
if (x_184 == 0)
{
obj* x_185; 
x_185 = lean::box(0);
x_26 = x_185;
goto lbl_27;
}
else
{
obj* x_190; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_190 = lean::box(0);
x_20 = x_190;
goto lbl_21;
}
}
else
{
uint32 x_191; uint8 x_192; 
x_191 = 1114112;
x_192 = x_178 < x_191;
if (x_192 == 0)
{
uint32 x_193; uint8 x_194; 
x_193 = 0;
x_194 = x_10 == x_193;
if (x_194 == 0)
{
obj* x_195; 
x_195 = lean::box(0);
x_26 = x_195;
goto lbl_27;
}
else
{
obj* x_200; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_200 = lean::box(0);
x_20 = x_200;
goto lbl_21;
}
}
else
{
uint8 x_201; 
x_201 = x_10 == x_178;
if (x_201 == 0)
{
obj* x_202; 
x_202 = lean::box(0);
x_26 = x_202;
goto lbl_27;
}
else
{
obj* x_207; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_207 = lean::box(0);
x_20 = x_207;
goto lbl_21;
}
}
}
}
else
{
uint8 x_208; 
x_208 = x_10 == x_178;
if (x_208 == 0)
{
obj* x_209; 
x_209 = lean::box(0);
x_26 = x_209;
goto lbl_27;
}
else
{
obj* x_214; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_214 = lean::box(0);
x_20 = x_214;
goto lbl_21;
}
}
}
lbl_31:
{
uint32 x_216; uint32 x_217; uint8 x_218; 
lean::dec(x_30);
x_216 = 110;
x_217 = 55296;
x_218 = x_216 < x_217;
if (x_218 == 0)
{
uint32 x_219; uint8 x_220; 
x_219 = 57343;
x_220 = x_219 < x_216;
if (x_220 == 0)
{
uint32 x_221; uint8 x_222; 
x_221 = 0;
x_222 = x_10 == x_221;
if (x_222 == 0)
{
obj* x_223; 
x_223 = lean::box(0);
x_28 = x_223;
goto lbl_29;
}
else
{
obj* x_228; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_228 = lean::box(0);
x_22 = x_228;
goto lbl_23;
}
}
else
{
uint32 x_229; uint8 x_230; 
x_229 = 1114112;
x_230 = x_216 < x_229;
if (x_230 == 0)
{
uint32 x_231; uint8 x_232; 
x_231 = 0;
x_232 = x_10 == x_231;
if (x_232 == 0)
{
obj* x_233; 
x_233 = lean::box(0);
x_28 = x_233;
goto lbl_29;
}
else
{
obj* x_238; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_238 = lean::box(0);
x_22 = x_238;
goto lbl_23;
}
}
else
{
uint8 x_239; 
x_239 = x_10 == x_216;
if (x_239 == 0)
{
obj* x_240; 
x_240 = lean::box(0);
x_28 = x_240;
goto lbl_29;
}
else
{
obj* x_245; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_245 = lean::box(0);
x_22 = x_245;
goto lbl_23;
}
}
}
}
else
{
uint8 x_246; 
x_246 = x_10 == x_216;
if (x_246 == 0)
{
obj* x_247; 
x_247 = lean::box(0);
x_28 = x_247;
goto lbl_29;
}
else
{
obj* x_252; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_252 = lean::box(0);
x_22 = x_252;
goto lbl_23;
}
}
}
lbl_33:
{
uint32 x_254; uint32 x_255; uint8 x_256; uint32 x_257; 
lean::dec(x_32);
x_254 = 39;
x_255 = 55296;
x_256 = x_254 < x_255;
if (x_256 == 0)
{
uint32 x_259; uint8 x_260; 
x_259 = 57343;
x_260 = x_259 < x_254;
if (x_260 == 0)
{
uint32 x_261; 
x_261 = 0;
x_257 = x_261;
goto lbl_258;
}
else
{
uint32 x_262; uint8 x_263; 
x_262 = 1114112;
x_263 = x_254 < x_262;
if (x_263 == 0)
{
uint32 x_264; 
x_264 = 0;
x_257 = x_264;
goto lbl_258;
}
else
{
x_257 = x_254;
goto lbl_258;
}
}
}
else
{
x_257 = x_254;
goto lbl_258;
}
lbl_258:
{
uint8 x_265; 
x_265 = x_10 == x_257;
if (x_265 == 0)
{
obj* x_266; 
x_266 = lean::box(0);
x_30 = x_266;
goto lbl_31;
}
else
{
obj* x_271; obj* x_274; obj* x_277; obj* x_278; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_271 = lean::cnstr_get(x_9, 0);
lean::inc(x_271);
lean::dec(x_9);
x_274 = lean::cnstr_get(x_271, 1);
lean::inc(x_274);
lean::dec(x_271);
x_277 = lean::box_uint32(x_257);
x_278 = lean::apply_2(x_274, lean::box(0), x_277);
return x_278;
}
}
}
lbl_35:
{
uint32 x_280; uint32 x_281; uint8 x_282; uint32 x_283; 
lean::dec(x_34);
x_280 = 34;
x_281 = 55296;
x_282 = x_280 < x_281;
if (x_282 == 0)
{
uint32 x_285; uint8 x_286; 
x_285 = 57343;
x_286 = x_285 < x_280;
if (x_286 == 0)
{
uint32 x_287; 
x_287 = 0;
x_283 = x_287;
goto lbl_284;
}
else
{
uint32 x_288; uint8 x_289; 
x_288 = 1114112;
x_289 = x_280 < x_288;
if (x_289 == 0)
{
uint32 x_290; 
x_290 = 0;
x_283 = x_290;
goto lbl_284;
}
else
{
x_283 = x_280;
goto lbl_284;
}
}
}
else
{
x_283 = x_280;
goto lbl_284;
}
lbl_284:
{
uint8 x_291; 
x_291 = x_10 == x_283;
if (x_291 == 0)
{
obj* x_292; 
x_292 = lean::box(0);
x_32 = x_292;
goto lbl_33;
}
else
{
obj* x_297; obj* x_300; obj* x_303; obj* x_304; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_297 = lean::cnstr_get(x_9, 0);
lean::inc(x_297);
lean::dec(x_9);
x_300 = lean::cnstr_get(x_297, 1);
lean::inc(x_300);
lean::dec(x_297);
x_303 = lean::box_uint32(x_283);
x_304 = lean::apply_2(x_300, lean::box(0), x_303);
return x_304;
}
}
}
lbl_40:
{
uint8 x_305; 
x_305 = x_10 == x_39;
if (x_305 == 0)
{
obj* x_306; 
x_306 = lean::box(0);
x_34 = x_306;
goto lbl_35;
}
else
{
obj* x_311; obj* x_314; obj* x_317; obj* x_318; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_311 = lean::cnstr_get(x_9, 0);
lean::inc(x_311);
lean::dec(x_9);
x_314 = lean::cnstr_get(x_311, 1);
lean::inc(x_314);
lean::dec(x_311);
x_317 = lean::box_uint32(x_39);
x_318 = lean::apply_2(x_314, lean::box(0), x_317);
return x_318;
}
}
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_14; obj* x_15; 
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_lean_parser_monad__parsec_any___rarg(x_0, x_1);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_2);
lean::inc(x_2);
lean::inc(x_2);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed), 11, 10);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_4);
lean::closure_set(x_14, 3, x_2);
lean::closure_set(x_14, 4, x_3);
lean::closure_set(x_14, 5, x_2);
lean::closure_set(x_14, 6, x_3);
lean::closure_set(x_14, 7, x_2);
lean::closure_set(x_14, 8, x_2);
lean::closure_set(x_14, 9, x_2);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_7, x_14);
return x_15;
}
}
obj* l_lean_parser_parse__quoted__char___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__8), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
lean::closure_set(x_11, 3, x_3);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
return x_12;
}
}
obj* l_lean_parser_parse__quoted__char(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint32 x_11; obj* x_12; 
x_11 = lean::unbox_uint32(x_10);
x_12 = l_lean_parser_parse__quoted__char___rarg___lambda__7(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__2___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__5___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__8___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint32 x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::string_push(x_0, x_5);
x_7 = l_lean_parser_parse__string__literal__aux___main___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint32 x_6) {
_start:
{
obj* x_7; uint32 x_9; uint32 x_10; uint8 x_11; uint32 x_12; 
x_9 = 92;
x_10 = 55296;
x_11 = x_9 < x_10;
if (x_11 == 0)
{
uint32 x_14; uint8 x_15; 
x_14 = 57343;
x_15 = x_14 < x_9;
if (x_15 == 0)
{
uint32 x_16; 
x_16 = 0;
x_12 = x_16;
goto lbl_13;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = 1114112;
x_18 = x_9 < x_17;
if (x_18 == 0)
{
uint32 x_19; 
x_19 = 0;
x_12 = x_19;
goto lbl_13;
}
else
{
x_12 = x_9;
goto lbl_13;
}
}
}
else
{
x_12 = x_9;
goto lbl_13;
}
lbl_8:
{
uint32 x_21; uint32 x_22; uint8 x_23; uint32 x_24; 
lean::dec(x_7);
x_21 = 34;
x_22 = 55296;
x_23 = x_21 < x_22;
if (x_23 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = 57343;
x_27 = x_26 < x_21;
if (x_27 == 0)
{
uint32 x_28; 
x_28 = 0;
x_24 = x_28;
goto lbl_25;
}
else
{
uint32 x_29; uint8 x_30; 
x_29 = 1114112;
x_30 = x_21 < x_29;
if (x_30 == 0)
{
uint32 x_31; 
x_31 = 0;
x_24 = x_31;
goto lbl_25;
}
else
{
x_24 = x_21;
goto lbl_25;
}
}
}
else
{
x_24 = x_21;
goto lbl_25;
}
lbl_25:
{
uint8 x_32; 
x_32 = x_6 == x_24;
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
x_33 = lean::string_push(x_0, x_6);
x_34 = l_lean_parser_parse__string__literal__aux___main___rarg(x_1, x_2, x_3, x_4, x_33);
return x_34;
}
else
{
obj* x_38; obj* x_41; obj* x_44; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
lean::dec(x_3);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = lean::apply_2(x_41, lean::box(0), x_0);
return x_44;
}
}
}
lbl_13:
{
uint8 x_45; 
x_45 = x_6 == x_12;
if (x_45 == 0)
{
obj* x_47; 
lean::dec(x_5);
x_47 = lean::box(0);
x_7 = x_47;
goto lbl_8;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_51 = l_lean_parser_parse__quoted__char___rarg(x_1, x_2, x_3);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_52, 0, x_0);
lean::closure_set(x_52, 1, x_1);
lean::closure_set(x_52, 2, x_2);
lean::closure_set(x_52, 3, x_3);
lean::closure_set(x_52, 4, x_4);
x_53 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_51, x_52);
return x_53;
}
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_16; obj* x_18; obj* x_19; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_8);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_lean_parser_monad__parsec_any___rarg(x_0, x_1);
lean::inc(x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2___boxed), 7, 6);
lean::closure_set(x_18, 0, x_4);
lean::closure_set(x_18, 1, x_0);
lean::closure_set(x_18, 2, x_1);
lean::closure_set(x_18, 3, x_2);
lean::closure_set(x_18, 4, x_9);
lean::closure_set(x_18, 5, x_12);
x_19 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_16, x_18);
return x_19;
}
else
{
obj* x_21; obj* x_24; uint32 x_26; uint32 x_27; uint8 x_28; obj* x_29; obj* x_32; 
lean::dec(x_3);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_21, 4);
lean::inc(x_24);
x_26 = 34;
x_27 = 55296;
x_28 = x_26 < x_27;
x_29 = lean::cnstr_get(x_21, 1);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::apply_2(x_29, lean::box(0), x_4);
if (x_28 == 0)
{
uint32 x_33; uint8 x_34; 
x_33 = 57343;
x_34 = x_33 < x_26;
if (x_34 == 0)
{
uint32 x_35; obj* x_36; obj* x_37; 
x_35 = 0;
x_36 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(x_0, x_1, x_35);
x_37 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_36, x_32);
return x_37;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 1114112;
x_39 = x_26 < x_38;
if (x_39 == 0)
{
uint32 x_40; obj* x_41; obj* x_42; 
x_40 = 0;
x_41 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(x_0, x_1, x_40);
x_42 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_41, x_32);
return x_42;
}
else
{
obj* x_43; obj* x_44; 
x_43 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(x_0, x_1, x_26);
x_44 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_43, x_32);
return x_44;
}
}
}
else
{
obj* x_45; obj* x_46; 
x_45 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(x_0, x_1, x_26);
x_46 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_45, x_32);
return x_46;
}
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal__aux___main___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_5);
x_7 = l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint32 x_7; obj* x_8; 
x_7 = lean::unbox_uint32(x_6);
x_8 = l_lean_parser_parse__string__literal__aux___main___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_lean_parser_parse__string__literal__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_parse__string__literal__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_parser_parse__string__literal__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal__aux___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__2___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__5___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__8___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__11___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = x_16 == x_2;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_4);
lean::dec(x_3);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_32 = lean::box_uint32(x_16);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_33, 0, x_4);
lean::closure_set(x_33, 1, x_32);
x_34 = lean::apply_2(x_3, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_parse__string__literal___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_string("");
x_5 = l_lean_parser_parse__string__literal__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_parser_parse__string__literal___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint32 x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_15);
x_17 = lean::apply_2(x_13, lean::box(0), x_15);
x_18 = l_lean_parser_monad__parsec_remaining___rarg___closed__1;
lean::inc(x_18);
x_20 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_18, x_17);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___rarg___lambda__1), 4, 3);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_1);
lean::closure_set(x_21, 2, x_2);
x_22 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_20, x_21);
return x_22;
}
}
obj* l_lean_parser_parse__string__literal___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint32 x_5; uint32 x_6; uint8 x_7; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = 34;
x_6 = 55296;
x_7 = x_5 < x_6;
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
lean::closure_set(x_11, 3, x_3);
if (x_7 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 57343;
x_13 = x_12 < x_5;
if (x_13 == 0)
{
uint32 x_14; obj* x_15; obj* x_16; 
x_14 = 0;
x_15 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(x_0, x_1, x_14);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = 1114112;
x_18 = x_5 < x_17;
if (x_18 == 0)
{
uint32 x_19; obj* x_20; obj* x_21; 
x_19 = 0;
x_20 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(x_0, x_1, x_19);
x_21 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_20, x_11);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
x_22 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(x_0, x_1, x_5);
x_23 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_22, x_11);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(x_0, x_1, x_5);
x_25 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_24, x_11);
return x_25;
}
}
}
obj* l_lean_parser_parse__string__literal(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_parse__string__literal___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_4);
x_6 = l_lean_parser_parse__string__literal___rarg___lambda__2(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
void initialize_init_lean_parser_parsec();
static bool _G_initialized = false;
void initialize_init_lean_parser_string__literal() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_parsec();
 l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1 = _init_l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1();
 l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1 = _init_l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1();
 l_lean_parser_parse__hex__digit___rarg___closed__1 = _init_l_lean_parser_parse__hex__digit___rarg___closed__1();
 l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1 = _init_l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1();
}
