// Lean compiler output
// Module: init.lean.parser.string_literal
// Imports: init.lean.parser.parsec
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint32);
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
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(obj*, obj*, uint32);
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7(obj*, obj*);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__quoted__char___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1(obj*, obj*);
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_parse__hex__digit___rarg___lambda__1(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(48u);
x_9 = lean::mk_nat_obj(55296u);
x_10 = lean::nat_dec_lt(x_8, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(57343u);
x_13 = lean::nat_dec_lt(x_12, x_8);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_8);
x_16 = lean::mk_nat_obj(0u);
x_17 = lean::box_uint32(x_1);
x_18 = lean::nat_sub(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_21 = lean::apply_2(x_5, lean::box(0), x_18);
return x_21;
}
else
{
obj* x_22; uint8 x_23; 
x_22 = lean::mk_nat_obj(1114112u);
x_23 = lean::nat_dec_lt(x_8, x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_31; 
lean::dec(x_8);
x_26 = lean::mk_nat_obj(0u);
x_27 = lean::box_uint32(x_1);
x_28 = lean::nat_sub(x_27, x_26);
lean::dec(x_26);
lean::dec(x_27);
x_31 = lean::apply_2(x_5, lean::box(0), x_28);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_36; 
x_32 = lean::box_uint32(x_1);
x_33 = lean::nat_sub(x_32, x_8);
lean::dec(x_8);
lean::dec(x_32);
x_36 = lean::apply_2(x_5, lean::box(0), x_33);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; obj* x_41; 
x_37 = lean::box_uint32(x_1);
x_38 = lean::nat_sub(x_37, x_8);
lean::dec(x_8);
lean::dec(x_37);
x_41 = lean::apply_2(x_5, lean::box(0), x_38);
return x_41;
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
uint32 x_15; obj* x_16; obj* x_18; obj* x_19; uint8 x_20; uint8 x_21; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = lean::mk_nat_obj(97u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_18);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
lean::dec(x_18);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::box_uint32(x_15);
x_29 = lean::nat_dec_le(x_27, x_28);
lean::dec(x_28);
lean::dec(x_27);
if (x_29 == 0)
{
obj* x_35; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_35 = lean::box(0);
x_16 = x_35;
goto lbl_17;
}
else
{
uint8 x_36; 
x_36 = 1;
x_21 = x_36;
goto lbl_22;
}
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::mk_nat_obj(1114112u);
x_38 = lean::nat_dec_lt(x_18, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_42; uint8 x_43; 
lean::dec(x_18);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::box_uint32(x_15);
x_43 = lean::nat_dec_le(x_41, x_42);
lean::dec(x_42);
lean::dec(x_41);
if (x_43 == 0)
{
obj* x_49; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_49 = lean::box(0);
x_16 = x_49;
goto lbl_17;
}
else
{
uint8 x_50; 
x_50 = 1;
x_21 = x_50;
goto lbl_22;
}
}
else
{
obj* x_51; uint8 x_52; 
x_51 = lean::box_uint32(x_15);
x_52 = lean::nat_dec_le(x_18, x_51);
lean::dec(x_51);
lean::dec(x_18);
if (x_52 == 0)
{
obj* x_58; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_58 = lean::box(0);
x_16 = x_58;
goto lbl_17;
}
else
{
uint8 x_59; 
x_59 = 1;
x_21 = x_59;
goto lbl_22;
}
}
}
}
else
{
obj* x_60; uint8 x_61; 
x_60 = lean::box_uint32(x_15);
x_61 = lean::nat_dec_le(x_18, x_60);
lean::dec(x_60);
lean::dec(x_18);
if (x_61 == 0)
{
obj* x_67; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_67 = lean::box(0);
x_16 = x_67;
goto lbl_17;
}
else
{
uint8 x_68; 
x_68 = 1;
x_21 = x_68;
goto lbl_22;
}
}
lbl_17:
{
obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_80; 
lean::dec(x_16);
x_70 = l_char_quote__core(x_15);
x_71 = l_char_has__repr___closed__1;
lean::inc(x_71);
x_73 = lean::string_append(x_71, x_70);
lean::dec(x_70);
x_75 = lean::string_append(x_73, x_71);
x_76 = lean::box(0);
x_77 = l_mjoin___rarg___closed__1;
lean::inc(x_76);
lean::inc(x_77);
x_80 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__2___rarg(x_1, lean::box(0), x_75, x_77, x_76, x_76);
return x_80;
}
lbl_22:
{
obj* x_81; uint8 x_82; 
x_81 = lean::mk_nat_obj(102u);
x_82 = lean::nat_dec_lt(x_81, x_19);
lean::dec(x_19);
if (x_82 == 0)
{
obj* x_84; uint8 x_85; 
x_84 = lean::mk_nat_obj(57343u);
x_85 = lean::nat_dec_lt(x_84, x_81);
lean::dec(x_84);
if (x_85 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
lean::dec(x_81);
x_88 = lean::mk_nat_obj(0u);
x_89 = lean::box_uint32(x_15);
x_90 = lean::nat_dec_le(x_89, x_88);
lean::dec(x_88);
if (x_90 == 0)
{
obj* x_95; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_89);
x_95 = lean::box(0);
x_16 = x_95;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_99; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_89);
x_99 = lean::box(0);
x_16 = x_99;
goto lbl_17;
}
else
{
obj* x_101; obj* x_102; 
lean::dec(x_1);
x_101 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_101, 0, x_3);
lean::closure_set(x_101, 1, x_89);
x_102 = lean::apply_2(x_2, lean::box(0), x_101);
return x_102;
}
}
}
else
{
obj* x_103; uint8 x_104; 
x_103 = lean::mk_nat_obj(1114112u);
x_104 = lean::nat_dec_lt(x_81, x_103);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_107; obj* x_108; uint8 x_109; 
lean::dec(x_81);
x_107 = lean::mk_nat_obj(0u);
x_108 = lean::box_uint32(x_15);
x_109 = lean::nat_dec_le(x_108, x_107);
lean::dec(x_107);
if (x_109 == 0)
{
obj* x_114; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_108);
x_114 = lean::box(0);
x_16 = x_114;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_118; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_108);
x_118 = lean::box(0);
x_16 = x_118;
goto lbl_17;
}
else
{
obj* x_120; obj* x_121; 
lean::dec(x_1);
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_120, 0, x_3);
lean::closure_set(x_120, 1, x_108);
x_121 = lean::apply_2(x_2, lean::box(0), x_120);
return x_121;
}
}
}
else
{
obj* x_122; uint8 x_123; 
x_122 = lean::box_uint32(x_15);
x_123 = lean::nat_dec_le(x_122, x_81);
lean::dec(x_81);
if (x_123 == 0)
{
obj* x_128; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_122);
x_128 = lean::box(0);
x_16 = x_128;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_132; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_122);
x_132 = lean::box(0);
x_16 = x_132;
goto lbl_17;
}
else
{
obj* x_134; obj* x_135; 
lean::dec(x_1);
x_134 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_134, 0, x_3);
lean::closure_set(x_134, 1, x_122);
x_135 = lean::apply_2(x_2, lean::box(0), x_134);
return x_135;
}
}
}
}
}
else
{
obj* x_136; uint8 x_137; 
x_136 = lean::box_uint32(x_15);
x_137 = lean::nat_dec_le(x_136, x_81);
lean::dec(x_81);
if (x_137 == 0)
{
obj* x_142; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_136);
x_142 = lean::box(0);
x_16 = x_142;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_146; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_136);
x_146 = lean::box(0);
x_16 = x_146;
goto lbl_17;
}
else
{
obj* x_148; obj* x_149; 
lean::dec(x_1);
x_148 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_148, 0, x_3);
lean::closure_set(x_148, 1, x_136);
x_149 = lean::apply_2(x_2, lean::box(0), x_148);
return x_149;
}
}
}
}
}
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__3(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(97u);
x_9 = lean::mk_nat_obj(55296u);
x_10 = lean::nat_dec_lt(x_8, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(57343u);
x_13 = lean::nat_dec_lt(x_12, x_8);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_25; 
lean::dec(x_8);
x_16 = lean::mk_nat_obj(0u);
x_17 = lean::box_uint32(x_1);
x_18 = lean::nat_sub(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_21 = lean::mk_nat_obj(10u);
x_22 = lean::nat_add(x_21, x_18);
lean::dec(x_18);
lean::dec(x_21);
x_25 = lean::apply_2(x_5, lean::box(0), x_22);
return x_25;
}
else
{
obj* x_26; uint8 x_27; 
x_26 = lean::mk_nat_obj(1114112u);
x_27 = lean::nat_dec_lt(x_8, x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_39; 
lean::dec(x_8);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::box_uint32(x_1);
x_32 = lean::nat_sub(x_31, x_30);
lean::dec(x_30);
lean::dec(x_31);
x_35 = lean::mk_nat_obj(10u);
x_36 = lean::nat_add(x_35, x_32);
lean::dec(x_32);
lean::dec(x_35);
x_39 = lean::apply_2(x_5, lean::box(0), x_36);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_44; obj* x_45; obj* x_48; 
x_40 = lean::box_uint32(x_1);
x_41 = lean::nat_sub(x_40, x_8);
lean::dec(x_8);
lean::dec(x_40);
x_44 = lean::mk_nat_obj(10u);
x_45 = lean::nat_add(x_44, x_41);
lean::dec(x_41);
lean::dec(x_44);
x_48 = lean::apply_2(x_5, lean::box(0), x_45);
return x_48;
}
}
}
else
{
obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_57; 
x_49 = lean::box_uint32(x_1);
x_50 = lean::nat_sub(x_49, x_8);
lean::dec(x_8);
lean::dec(x_49);
x_53 = lean::mk_nat_obj(10u);
x_54 = lean::nat_add(x_53, x_50);
lean::dec(x_50);
lean::dec(x_53);
x_57 = lean::apply_2(x_5, lean::box(0), x_54);
return x_57;
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
uint32 x_15; obj* x_16; obj* x_18; obj* x_19; uint8 x_20; uint8 x_21; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = lean::mk_nat_obj(65u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_18);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
lean::dec(x_18);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::box_uint32(x_15);
x_29 = lean::nat_dec_le(x_27, x_28);
lean::dec(x_28);
lean::dec(x_27);
if (x_29 == 0)
{
obj* x_35; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_35 = lean::box(0);
x_16 = x_35;
goto lbl_17;
}
else
{
uint8 x_36; 
x_36 = 1;
x_21 = x_36;
goto lbl_22;
}
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::mk_nat_obj(1114112u);
x_38 = lean::nat_dec_lt(x_18, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_42; uint8 x_43; 
lean::dec(x_18);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::box_uint32(x_15);
x_43 = lean::nat_dec_le(x_41, x_42);
lean::dec(x_42);
lean::dec(x_41);
if (x_43 == 0)
{
obj* x_49; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_49 = lean::box(0);
x_16 = x_49;
goto lbl_17;
}
else
{
uint8 x_50; 
x_50 = 1;
x_21 = x_50;
goto lbl_22;
}
}
else
{
obj* x_51; uint8 x_52; 
x_51 = lean::box_uint32(x_15);
x_52 = lean::nat_dec_le(x_18, x_51);
lean::dec(x_51);
lean::dec(x_18);
if (x_52 == 0)
{
obj* x_58; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_58 = lean::box(0);
x_16 = x_58;
goto lbl_17;
}
else
{
uint8 x_59; 
x_59 = 1;
x_21 = x_59;
goto lbl_22;
}
}
}
}
else
{
obj* x_60; uint8 x_61; 
x_60 = lean::box_uint32(x_15);
x_61 = lean::nat_dec_le(x_18, x_60);
lean::dec(x_60);
lean::dec(x_18);
if (x_61 == 0)
{
obj* x_67; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_2);
x_67 = lean::box(0);
x_16 = x_67;
goto lbl_17;
}
else
{
uint8 x_68; 
x_68 = 1;
x_21 = x_68;
goto lbl_22;
}
}
lbl_17:
{
obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_80; 
lean::dec(x_16);
x_70 = l_char_quote__core(x_15);
x_71 = l_char_has__repr___closed__1;
lean::inc(x_71);
x_73 = lean::string_append(x_71, x_70);
lean::dec(x_70);
x_75 = lean::string_append(x_73, x_71);
x_76 = lean::box(0);
x_77 = l_mjoin___rarg___closed__1;
lean::inc(x_76);
lean::inc(x_77);
x_80 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__hex__digit___spec__4___rarg(x_1, lean::box(0), x_75, x_77, x_76, x_76);
return x_80;
}
lbl_22:
{
obj* x_81; uint8 x_82; 
x_81 = lean::mk_nat_obj(70u);
x_82 = lean::nat_dec_lt(x_81, x_19);
lean::dec(x_19);
if (x_82 == 0)
{
obj* x_84; uint8 x_85; 
x_84 = lean::mk_nat_obj(57343u);
x_85 = lean::nat_dec_lt(x_84, x_81);
lean::dec(x_84);
if (x_85 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
lean::dec(x_81);
x_88 = lean::mk_nat_obj(0u);
x_89 = lean::box_uint32(x_15);
x_90 = lean::nat_dec_le(x_89, x_88);
lean::dec(x_88);
if (x_90 == 0)
{
obj* x_95; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_89);
x_95 = lean::box(0);
x_16 = x_95;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_99; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_89);
x_99 = lean::box(0);
x_16 = x_99;
goto lbl_17;
}
else
{
obj* x_101; obj* x_102; 
lean::dec(x_1);
x_101 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_101, 0, x_3);
lean::closure_set(x_101, 1, x_89);
x_102 = lean::apply_2(x_2, lean::box(0), x_101);
return x_102;
}
}
}
else
{
obj* x_103; uint8 x_104; 
x_103 = lean::mk_nat_obj(1114112u);
x_104 = lean::nat_dec_lt(x_81, x_103);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_107; obj* x_108; uint8 x_109; 
lean::dec(x_81);
x_107 = lean::mk_nat_obj(0u);
x_108 = lean::box_uint32(x_15);
x_109 = lean::nat_dec_le(x_108, x_107);
lean::dec(x_107);
if (x_109 == 0)
{
obj* x_114; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_108);
x_114 = lean::box(0);
x_16 = x_114;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_118; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_108);
x_118 = lean::box(0);
x_16 = x_118;
goto lbl_17;
}
else
{
obj* x_120; obj* x_121; 
lean::dec(x_1);
x_120 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_120, 0, x_3);
lean::closure_set(x_120, 1, x_108);
x_121 = lean::apply_2(x_2, lean::box(0), x_120);
return x_121;
}
}
}
else
{
obj* x_122; uint8 x_123; 
x_122 = lean::box_uint32(x_15);
x_123 = lean::nat_dec_le(x_122, x_81);
lean::dec(x_81);
if (x_123 == 0)
{
obj* x_128; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_122);
x_128 = lean::box(0);
x_16 = x_128;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_132; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_122);
x_132 = lean::box(0);
x_16 = x_132;
goto lbl_17;
}
else
{
obj* x_134; obj* x_135; 
lean::dec(x_1);
x_134 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_134, 0, x_3);
lean::closure_set(x_134, 1, x_122);
x_135 = lean::apply_2(x_2, lean::box(0), x_134);
return x_135;
}
}
}
}
}
else
{
obj* x_136; uint8 x_137; 
x_136 = lean::box_uint32(x_15);
x_137 = lean::nat_dec_le(x_136, x_81);
lean::dec(x_81);
if (x_137 == 0)
{
obj* x_142; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_136);
x_142 = lean::box(0);
x_16 = x_142;
goto lbl_17;
}
else
{
if (x_21 == 0)
{
obj* x_146; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_136);
x_146 = lean::box(0);
x_16 = x_146;
goto lbl_17;
}
else
{
obj* x_148; obj* x_149; 
lean::dec(x_1);
x_148 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_148, 0, x_3);
lean::closure_set(x_148, 1, x_136);
x_149 = lean::apply_2(x_2, lean::box(0), x_148);
return x_149;
}
}
}
}
}
}
}
obj* l_lean_parser_parse__hex__digit___rarg___lambda__5(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(65u);
x_9 = lean::mk_nat_obj(55296u);
x_10 = lean::nat_dec_lt(x_8, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(57343u);
x_13 = lean::nat_dec_lt(x_12, x_8);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_25; 
lean::dec(x_8);
x_16 = lean::mk_nat_obj(0u);
x_17 = lean::box_uint32(x_1);
x_18 = lean::nat_sub(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_21 = lean::mk_nat_obj(10u);
x_22 = lean::nat_add(x_21, x_18);
lean::dec(x_18);
lean::dec(x_21);
x_25 = lean::apply_2(x_5, lean::box(0), x_22);
return x_25;
}
else
{
obj* x_26; uint8 x_27; 
x_26 = lean::mk_nat_obj(1114112u);
x_27 = lean::nat_dec_lt(x_8, x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_36; obj* x_39; 
lean::dec(x_8);
x_30 = lean::mk_nat_obj(0u);
x_31 = lean::box_uint32(x_1);
x_32 = lean::nat_sub(x_31, x_30);
lean::dec(x_30);
lean::dec(x_31);
x_35 = lean::mk_nat_obj(10u);
x_36 = lean::nat_add(x_35, x_32);
lean::dec(x_32);
lean::dec(x_35);
x_39 = lean::apply_2(x_5, lean::box(0), x_36);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_44; obj* x_45; obj* x_48; 
x_40 = lean::box_uint32(x_1);
x_41 = lean::nat_sub(x_40, x_8);
lean::dec(x_8);
lean::dec(x_40);
x_44 = lean::mk_nat_obj(10u);
x_45 = lean::nat_add(x_44, x_41);
lean::dec(x_41);
lean::dec(x_44);
x_48 = lean::apply_2(x_5, lean::box(0), x_45);
return x_48;
}
}
}
else
{
obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_57; 
x_49 = lean::box_uint32(x_1);
x_50 = lean::nat_sub(x_49, x_8);
lean::dec(x_8);
lean::dec(x_49);
x_53 = lean::mk_nat_obj(10u);
x_54 = lean::nat_add(x_53, x_50);
lean::dec(x_50);
lean::dec(x_53);
x_57 = lean::apply_2(x_5, lean::box(0), x_54);
return x_57;
}
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
obj* l_lean_parser_parse__quoted__char___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_28; uint8 x_29; 
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
x_28 = lean::mk_nat_obj(55296u);
x_29 = lean::nat_dec_lt(x_25, x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(57343u);
x_32 = lean::nat_dec_lt(x_31, x_25);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_35; obj* x_36; 
lean::dec(x_25);
x_35 = lean::mk_nat_obj(0u);
x_36 = lean::apply_2(x_8, lean::box(0), x_35);
return x_36;
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::mk_nat_obj(1114112u);
x_38 = lean::nat_dec_lt(x_25, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_25);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::apply_2(x_8, lean::box(0), x_41);
return x_42;
}
else
{
obj* x_43; 
x_43 = lean::apply_2(x_8, lean::box(0), x_25);
return x_43;
}
}
}
else
{
obj* x_44; 
x_44 = lean::apply_2(x_8, lean::box(0), x_25);
return x_44;
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
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_16; uint8 x_17; 
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
x_16 = lean::mk_nat_obj(55296u);
x_17 = lean::nat_dec_lt(x_13, x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = lean::mk_nat_obj(57343u);
x_20 = lean::nat_dec_lt(x_19, x_13);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_13);
x_23 = lean::mk_nat_obj(0u);
x_24 = lean::apply_2(x_6, lean::box(0), x_23);
return x_24;
}
else
{
obj* x_25; uint8 x_26; 
x_25 = lean::mk_nat_obj(1114112u);
x_26 = lean::nat_dec_lt(x_13, x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_13);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::apply_2(x_6, lean::box(0), x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::apply_2(x_6, lean::box(0), x_13);
return x_31;
}
}
}
else
{
obj* x_32; 
x_32 = lean::apply_2(x_6, lean::box(0), x_13);
return x_32;
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
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint32 x_8) {
_start:
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; uint8 x_30; uint32 x_32; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_28 = lean::mk_nat_obj(92u);
x_29 = lean::mk_nat_obj(55296u);
x_30 = lean::nat_dec_lt(x_28, x_29);
lean::dec(x_29);
if (x_30 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = lean::mk_nat_obj(57343u);
x_35 = lean::nat_dec_lt(x_34, x_28);
lean::dec(x_34);
if (x_35 == 0)
{
obj* x_38; uint32 x_39; 
lean::dec(x_28);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean::unbox_uint32(x_38);
lean::dec(x_38);
x_32 = x_39;
goto lbl_33;
}
else
{
obj* x_41; uint8 x_42; 
x_41 = lean::mk_nat_obj(1114112u);
x_42 = lean::nat_dec_lt(x_28, x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_45; uint32 x_46; 
lean::dec(x_28);
x_45 = lean::mk_nat_obj(0u);
x_46 = lean::unbox_uint32(x_45);
lean::dec(x_45);
x_32 = x_46;
goto lbl_33;
}
else
{
uint32 x_48; 
x_48 = lean::unbox_uint32(x_28);
lean::dec(x_28);
x_32 = x_48;
goto lbl_33;
}
}
}
else
{
uint32 x_50; 
x_50 = lean::unbox_uint32(x_28);
lean::dec(x_28);
x_32 = x_50;
goto lbl_33;
}
lbl_13:
{
obj* x_54; obj* x_57; obj* x_58; 
lean::dec(x_12);
lean::inc(x_7);
x_54 = l_lean_parser_parse__hex__digit___rarg(x_0, x_1, x_7);
lean::inc(x_54);
lean::inc(x_6);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__4), 4, 3);
lean::closure_set(x_57, 0, x_7);
lean::closure_set(x_57, 1, x_6);
lean::closure_set(x_57, 2, x_54);
x_58 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_54, x_57);
return x_58;
}
lbl_15:
{
obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_14);
lean::inc(x_7);
x_61 = l_lean_parser_parse__hex__digit___rarg(x_0, x_1, x_7);
lean::inc(x_61);
lean::inc(x_6);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__6), 4, 3);
lean::closure_set(x_64, 0, x_7);
lean::closure_set(x_64, 1, x_6);
lean::closure_set(x_64, 2, x_61);
x_65 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_61, x_64);
return x_65;
}
lbl_17:
{
obj* x_67; obj* x_68; uint8 x_69; 
lean::dec(x_16);
x_67 = lean::mk_nat_obj(117u);
x_68 = lean::mk_nat_obj(55296u);
x_69 = lean::nat_dec_lt(x_67, x_68);
lean::dec(x_68);
if (x_69 == 0)
{
obj* x_71; uint8 x_72; 
x_71 = lean::mk_nat_obj(57343u);
x_72 = lean::nat_dec_lt(x_71, x_67);
lean::dec(x_71);
if (x_72 == 0)
{
obj* x_75; obj* x_76; uint8 x_77; 
lean::dec(x_67);
x_75 = lean::mk_nat_obj(0u);
x_76 = lean::box_uint32(x_8);
x_77 = lean::nat_dec_eq(x_76, x_75);
lean::dec(x_75);
lean::dec(x_76);
if (x_77 == 0)
{
obj* x_82; obj* x_84; 
lean::dec(x_7);
lean::dec(x_6);
x_82 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__1___rarg(x_0, x_1, lean::box(0), x_82, x_2);
return x_84;
}
else
{
obj* x_86; 
lean::dec(x_2);
x_86 = lean::box(0);
x_12 = x_86;
goto lbl_13;
}
}
else
{
obj* x_87; uint8 x_88; 
x_87 = lean::mk_nat_obj(1114112u);
x_88 = lean::nat_dec_lt(x_67, x_87);
lean::dec(x_87);
if (x_88 == 0)
{
obj* x_91; obj* x_92; uint8 x_93; 
lean::dec(x_67);
x_91 = lean::mk_nat_obj(0u);
x_92 = lean::box_uint32(x_8);
x_93 = lean::nat_dec_eq(x_92, x_91);
lean::dec(x_91);
lean::dec(x_92);
if (x_93 == 0)
{
obj* x_98; obj* x_100; 
lean::dec(x_7);
lean::dec(x_6);
x_98 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_98);
x_100 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__3___rarg(x_0, x_1, lean::box(0), x_98, x_2);
return x_100;
}
else
{
obj* x_102; 
lean::dec(x_2);
x_102 = lean::box(0);
x_12 = x_102;
goto lbl_13;
}
}
else
{
obj* x_103; uint8 x_104; 
x_103 = lean::box_uint32(x_8);
x_104 = lean::nat_dec_eq(x_103, x_67);
lean::dec(x_67);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_109; obj* x_111; 
lean::dec(x_7);
lean::dec(x_6);
x_109 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_109);
x_111 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__5___rarg(x_0, x_1, lean::box(0), x_109, x_2);
return x_111;
}
else
{
obj* x_113; 
lean::dec(x_2);
x_113 = lean::box(0);
x_12 = x_113;
goto lbl_13;
}
}
}
}
else
{
obj* x_114; uint8 x_115; 
x_114 = lean::box_uint32(x_8);
x_115 = lean::nat_dec_eq(x_114, x_67);
lean::dec(x_67);
lean::dec(x_114);
if (x_115 == 0)
{
obj* x_120; obj* x_122; 
lean::dec(x_7);
lean::dec(x_6);
x_120 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_120);
x_122 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_parse__quoted__char___spec__7___rarg(x_0, x_1, lean::box(0), x_120, x_2);
return x_122;
}
else
{
obj* x_124; 
lean::dec(x_2);
x_124 = lean::box(0);
x_12 = x_124;
goto lbl_13;
}
}
}
lbl_19:
{
obj* x_126; obj* x_127; uint8 x_128; 
lean::dec(x_18);
x_126 = lean::mk_nat_obj(120u);
x_127 = lean::mk_nat_obj(55296u);
x_128 = lean::nat_dec_lt(x_126, x_127);
lean::dec(x_127);
if (x_128 == 0)
{
obj* x_130; uint8 x_131; 
x_130 = lean::mk_nat_obj(57343u);
x_131 = lean::nat_dec_lt(x_130, x_126);
lean::dec(x_130);
if (x_131 == 0)
{
obj* x_134; obj* x_135; uint8 x_136; 
lean::dec(x_126);
x_134 = lean::mk_nat_obj(0u);
x_135 = lean::box_uint32(x_8);
x_136 = lean::nat_dec_eq(x_135, x_134);
lean::dec(x_134);
lean::dec(x_135);
if (x_136 == 0)
{
obj* x_139; 
x_139 = lean::box(0);
x_16 = x_139;
goto lbl_17;
}
else
{
obj* x_141; 
lean::dec(x_2);
x_141 = lean::box(0);
x_14 = x_141;
goto lbl_15;
}
}
else
{
obj* x_142; uint8 x_143; 
x_142 = lean::mk_nat_obj(1114112u);
x_143 = lean::nat_dec_lt(x_126, x_142);
lean::dec(x_142);
if (x_143 == 0)
{
obj* x_146; obj* x_147; uint8 x_148; 
lean::dec(x_126);
x_146 = lean::mk_nat_obj(0u);
x_147 = lean::box_uint32(x_8);
x_148 = lean::nat_dec_eq(x_147, x_146);
lean::dec(x_146);
lean::dec(x_147);
if (x_148 == 0)
{
obj* x_151; 
x_151 = lean::box(0);
x_16 = x_151;
goto lbl_17;
}
else
{
obj* x_153; 
lean::dec(x_2);
x_153 = lean::box(0);
x_14 = x_153;
goto lbl_15;
}
}
else
{
obj* x_154; uint8 x_155; 
x_154 = lean::box_uint32(x_8);
x_155 = lean::nat_dec_eq(x_154, x_126);
lean::dec(x_126);
lean::dec(x_154);
if (x_155 == 0)
{
obj* x_158; 
x_158 = lean::box(0);
x_16 = x_158;
goto lbl_17;
}
else
{
obj* x_160; 
lean::dec(x_2);
x_160 = lean::box(0);
x_14 = x_160;
goto lbl_15;
}
}
}
}
else
{
obj* x_161; uint8 x_162; 
x_161 = lean::box_uint32(x_8);
x_162 = lean::nat_dec_eq(x_161, x_126);
lean::dec(x_126);
lean::dec(x_161);
if (x_162 == 0)
{
obj* x_165; 
x_165 = lean::box(0);
x_16 = x_165;
goto lbl_17;
}
else
{
obj* x_167; 
lean::dec(x_2);
x_167 = lean::box(0);
x_14 = x_167;
goto lbl_15;
}
}
}
lbl_21:
{
obj* x_169; obj* x_170; uint8 x_171; uint32 x_172; 
lean::dec(x_20);
x_169 = lean::mk_nat_obj(116u);
x_170 = lean::mk_nat_obj(55296u);
x_171 = lean::nat_dec_lt(x_169, x_170);
if (x_171 == 0)
{
obj* x_174; uint8 x_175; 
x_174 = lean::mk_nat_obj(57343u);
x_175 = lean::nat_dec_lt(x_174, x_169);
lean::dec(x_174);
if (x_175 == 0)
{
obj* x_178; uint32 x_179; 
lean::dec(x_169);
x_178 = lean::mk_nat_obj(0u);
x_179 = lean::unbox_uint32(x_178);
lean::dec(x_178);
x_172 = x_179;
goto lbl_173;
}
else
{
obj* x_181; uint8 x_182; 
x_181 = lean::mk_nat_obj(1114112u);
x_182 = lean::nat_dec_lt(x_169, x_181);
lean::dec(x_181);
if (x_182 == 0)
{
obj* x_185; uint32 x_186; 
lean::dec(x_169);
x_185 = lean::mk_nat_obj(0u);
x_186 = lean::unbox_uint32(x_185);
lean::dec(x_185);
x_172 = x_186;
goto lbl_173;
}
else
{
uint32 x_188; 
x_188 = lean::unbox_uint32(x_169);
lean::dec(x_169);
x_172 = x_188;
goto lbl_173;
}
}
}
else
{
uint32 x_190; 
x_190 = lean::unbox_uint32(x_169);
lean::dec(x_169);
x_172 = x_190;
goto lbl_173;
}
lbl_173:
{
obj* x_192; obj* x_193; uint8 x_194; 
x_192 = lean::box_uint32(x_8);
x_193 = lean::box_uint32(x_172);
x_194 = lean::nat_dec_eq(x_192, x_193);
lean::dec(x_193);
lean::dec(x_192);
if (x_194 == 0)
{
obj* x_198; 
lean::dec(x_170);
x_198 = lean::box(0);
x_18 = x_198;
goto lbl_19;
}
else
{
obj* x_203; obj* x_206; obj* x_209; uint8 x_210; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_203 = lean::cnstr_get(x_7, 0);
lean::inc(x_203);
lean::dec(x_7);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
x_209 = lean::mk_nat_obj(9u);
x_210 = lean::nat_dec_lt(x_209, x_170);
lean::dec(x_170);
if (x_210 == 0)
{
obj* x_212; uint8 x_213; 
x_212 = lean::mk_nat_obj(57343u);
x_213 = lean::nat_dec_lt(x_212, x_209);
lean::dec(x_212);
if (x_213 == 0)
{
obj* x_216; obj* x_217; 
lean::dec(x_209);
x_216 = lean::mk_nat_obj(0u);
x_217 = lean::apply_2(x_206, lean::box(0), x_216);
return x_217;
}
else
{
obj* x_218; uint8 x_219; 
x_218 = lean::mk_nat_obj(1114112u);
x_219 = lean::nat_dec_lt(x_209, x_218);
lean::dec(x_218);
if (x_219 == 0)
{
obj* x_222; obj* x_223; 
lean::dec(x_209);
x_222 = lean::mk_nat_obj(0u);
x_223 = lean::apply_2(x_206, lean::box(0), x_222);
return x_223;
}
else
{
obj* x_224; 
x_224 = lean::apply_2(x_206, lean::box(0), x_209);
return x_224;
}
}
}
else
{
obj* x_225; 
x_225 = lean::apply_2(x_206, lean::box(0), x_209);
return x_225;
}
}
}
}
lbl_23:
{
obj* x_227; obj* x_228; uint8 x_229; uint32 x_230; 
lean::dec(x_22);
x_227 = lean::mk_nat_obj(110u);
x_228 = lean::mk_nat_obj(55296u);
x_229 = lean::nat_dec_lt(x_227, x_228);
if (x_229 == 0)
{
obj* x_232; uint8 x_233; 
x_232 = lean::mk_nat_obj(57343u);
x_233 = lean::nat_dec_lt(x_232, x_227);
lean::dec(x_232);
if (x_233 == 0)
{
obj* x_236; uint32 x_237; 
lean::dec(x_227);
x_236 = lean::mk_nat_obj(0u);
x_237 = lean::unbox_uint32(x_236);
lean::dec(x_236);
x_230 = x_237;
goto lbl_231;
}
else
{
obj* x_239; uint8 x_240; 
x_239 = lean::mk_nat_obj(1114112u);
x_240 = lean::nat_dec_lt(x_227, x_239);
lean::dec(x_239);
if (x_240 == 0)
{
obj* x_243; uint32 x_244; 
lean::dec(x_227);
x_243 = lean::mk_nat_obj(0u);
x_244 = lean::unbox_uint32(x_243);
lean::dec(x_243);
x_230 = x_244;
goto lbl_231;
}
else
{
uint32 x_246; 
x_246 = lean::unbox_uint32(x_227);
lean::dec(x_227);
x_230 = x_246;
goto lbl_231;
}
}
}
else
{
uint32 x_248; 
x_248 = lean::unbox_uint32(x_227);
lean::dec(x_227);
x_230 = x_248;
goto lbl_231;
}
lbl_231:
{
obj* x_250; obj* x_251; uint8 x_252; 
x_250 = lean::box_uint32(x_8);
x_251 = lean::box_uint32(x_230);
x_252 = lean::nat_dec_eq(x_250, x_251);
lean::dec(x_251);
lean::dec(x_250);
if (x_252 == 0)
{
obj* x_256; 
lean::dec(x_228);
x_256 = lean::box(0);
x_20 = x_256;
goto lbl_21;
}
else
{
obj* x_261; obj* x_264; obj* x_267; uint8 x_268; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_261 = lean::cnstr_get(x_7, 0);
lean::inc(x_261);
lean::dec(x_7);
x_264 = lean::cnstr_get(x_261, 1);
lean::inc(x_264);
lean::dec(x_261);
x_267 = lean::mk_nat_obj(10u);
x_268 = lean::nat_dec_lt(x_267, x_228);
lean::dec(x_228);
if (x_268 == 0)
{
obj* x_270; uint8 x_271; 
x_270 = lean::mk_nat_obj(57343u);
x_271 = lean::nat_dec_lt(x_270, x_267);
lean::dec(x_270);
if (x_271 == 0)
{
obj* x_274; obj* x_275; 
lean::dec(x_267);
x_274 = lean::mk_nat_obj(0u);
x_275 = lean::apply_2(x_264, lean::box(0), x_274);
return x_275;
}
else
{
obj* x_276; uint8 x_277; 
x_276 = lean::mk_nat_obj(1114112u);
x_277 = lean::nat_dec_lt(x_267, x_276);
lean::dec(x_276);
if (x_277 == 0)
{
obj* x_280; obj* x_281; 
lean::dec(x_267);
x_280 = lean::mk_nat_obj(0u);
x_281 = lean::apply_2(x_264, lean::box(0), x_280);
return x_281;
}
else
{
obj* x_282; 
x_282 = lean::apply_2(x_264, lean::box(0), x_267);
return x_282;
}
}
}
else
{
obj* x_283; 
x_283 = lean::apply_2(x_264, lean::box(0), x_267);
return x_283;
}
}
}
}
lbl_25:
{
obj* x_285; obj* x_286; uint8 x_287; uint32 x_289; 
lean::dec(x_24);
x_285 = lean::mk_nat_obj(39u);
x_286 = lean::mk_nat_obj(55296u);
x_287 = lean::nat_dec_lt(x_285, x_286);
lean::dec(x_286);
if (x_287 == 0)
{
obj* x_291; uint8 x_292; 
x_291 = lean::mk_nat_obj(57343u);
x_292 = lean::nat_dec_lt(x_291, x_285);
lean::dec(x_291);
if (x_292 == 0)
{
obj* x_295; uint32 x_296; 
lean::dec(x_285);
x_295 = lean::mk_nat_obj(0u);
x_296 = lean::unbox_uint32(x_295);
lean::dec(x_295);
x_289 = x_296;
goto lbl_290;
}
else
{
obj* x_298; uint8 x_299; 
x_298 = lean::mk_nat_obj(1114112u);
x_299 = lean::nat_dec_lt(x_285, x_298);
lean::dec(x_298);
if (x_299 == 0)
{
obj* x_302; uint32 x_303; 
lean::dec(x_285);
x_302 = lean::mk_nat_obj(0u);
x_303 = lean::unbox_uint32(x_302);
lean::dec(x_302);
x_289 = x_303;
goto lbl_290;
}
else
{
uint32 x_305; 
x_305 = lean::unbox_uint32(x_285);
lean::dec(x_285);
x_289 = x_305;
goto lbl_290;
}
}
}
else
{
uint32 x_307; 
x_307 = lean::unbox_uint32(x_285);
lean::dec(x_285);
x_289 = x_307;
goto lbl_290;
}
lbl_290:
{
obj* x_309; obj* x_310; uint8 x_311; 
x_309 = lean::box_uint32(x_8);
x_310 = lean::box_uint32(x_289);
x_311 = lean::nat_dec_eq(x_309, x_310);
lean::dec(x_309);
if (x_311 == 0)
{
obj* x_314; 
lean::dec(x_310);
x_314 = lean::box(0);
x_22 = x_314;
goto lbl_23;
}
else
{
obj* x_319; obj* x_322; obj* x_325; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_319 = lean::cnstr_get(x_7, 0);
lean::inc(x_319);
lean::dec(x_7);
x_322 = lean::cnstr_get(x_319, 1);
lean::inc(x_322);
lean::dec(x_319);
x_325 = lean::apply_2(x_322, lean::box(0), x_310);
return x_325;
}
}
}
lbl_27:
{
obj* x_327; obj* x_328; uint8 x_329; uint32 x_331; 
lean::dec(x_26);
x_327 = lean::mk_nat_obj(34u);
x_328 = lean::mk_nat_obj(55296u);
x_329 = lean::nat_dec_lt(x_327, x_328);
lean::dec(x_328);
if (x_329 == 0)
{
obj* x_333; uint8 x_334; 
x_333 = lean::mk_nat_obj(57343u);
x_334 = lean::nat_dec_lt(x_333, x_327);
lean::dec(x_333);
if (x_334 == 0)
{
obj* x_337; uint32 x_338; 
lean::dec(x_327);
x_337 = lean::mk_nat_obj(0u);
x_338 = lean::unbox_uint32(x_337);
lean::dec(x_337);
x_331 = x_338;
goto lbl_332;
}
else
{
obj* x_340; uint8 x_341; 
x_340 = lean::mk_nat_obj(1114112u);
x_341 = lean::nat_dec_lt(x_327, x_340);
lean::dec(x_340);
if (x_341 == 0)
{
obj* x_344; uint32 x_345; 
lean::dec(x_327);
x_344 = lean::mk_nat_obj(0u);
x_345 = lean::unbox_uint32(x_344);
lean::dec(x_344);
x_331 = x_345;
goto lbl_332;
}
else
{
uint32 x_347; 
x_347 = lean::unbox_uint32(x_327);
lean::dec(x_327);
x_331 = x_347;
goto lbl_332;
}
}
}
else
{
uint32 x_349; 
x_349 = lean::unbox_uint32(x_327);
lean::dec(x_327);
x_331 = x_349;
goto lbl_332;
}
lbl_332:
{
obj* x_351; obj* x_352; uint8 x_353; 
x_351 = lean::box_uint32(x_8);
x_352 = lean::box_uint32(x_331);
x_353 = lean::nat_dec_eq(x_351, x_352);
lean::dec(x_351);
if (x_353 == 0)
{
obj* x_356; 
lean::dec(x_352);
x_356 = lean::box(0);
x_24 = x_356;
goto lbl_25;
}
else
{
obj* x_361; obj* x_364; obj* x_367; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_361 = lean::cnstr_get(x_7, 0);
lean::inc(x_361);
lean::dec(x_7);
x_364 = lean::cnstr_get(x_361, 1);
lean::inc(x_364);
lean::dec(x_361);
x_367 = lean::apply_2(x_364, lean::box(0), x_352);
return x_367;
}
}
}
lbl_33:
{
obj* x_368; obj* x_369; uint8 x_370; 
x_368 = lean::box_uint32(x_8);
x_369 = lean::box_uint32(x_32);
x_370 = lean::nat_dec_eq(x_368, x_369);
lean::dec(x_368);
if (x_370 == 0)
{
obj* x_373; 
lean::dec(x_369);
x_373 = lean::box(0);
x_26 = x_373;
goto lbl_27;
}
else
{
obj* x_378; obj* x_381; obj* x_384; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_378 = lean::cnstr_get(x_7, 0);
lean::inc(x_378);
lean::dec(x_7);
x_381 = lean::cnstr_get(x_378, 1);
lean::inc(x_381);
lean::dec(x_378);
x_384 = lean::apply_2(x_381, lean::box(0), x_369);
return x_384;
}
}
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
obj* l_lean_parser_parse__quoted__char___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_12; obj* x_13; 
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_lean_parser_monad__parsec_any___rarg(x_0, x_1);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed), 9, 8);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_4);
lean::closure_set(x_12, 3, x_2);
lean::closure_set(x_12, 4, x_3);
lean::closure_set(x_12, 5, x_2);
lean::closure_set(x_12, 6, x_3);
lean::closure_set(x_12, 7, x_2);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_7, x_12);
return x_13;
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
obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint32 x_9; obj* x_10; 
x_9 = lean::unbox_uint32(x_8);
x_10 = l_lean_parser_parse__quoted__char___rarg___lambda__7(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__3___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__6___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__9___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal__aux___main___spec__12___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
obj* l_lean_parser_parse__string__literal__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_12; obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_5);
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
obj* x_21; obj* x_24; obj* x_26; obj* x_27; uint8 x_28; obj* x_30; obj* x_33; 
lean::dec(x_3);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_21, 4);
lean::inc(x_24);
x_26 = lean::mk_nat_obj(34u);
x_27 = lean::mk_nat_obj(55296u);
x_28 = lean::nat_dec_lt(x_26, x_27);
lean::dec(x_27);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::apply_2(x_30, lean::box(0), x_4);
if (x_28 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = lean::mk_nat_obj(57343u);
x_35 = lean::nat_dec_lt(x_34, x_26);
lean::dec(x_34);
if (x_35 == 0)
{
uint32 x_38; obj* x_40; obj* x_41; 
lean::dec(x_26);
x_38 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_40 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(x_0, x_1, x_38);
x_41 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_40, x_33);
return x_41;
}
else
{
obj* x_42; uint8 x_43; 
x_42 = lean::mk_nat_obj(1114112u);
x_43 = lean::nat_dec_lt(x_26, x_42);
lean::dec(x_42);
if (x_43 == 0)
{
uint32 x_46; obj* x_48; obj* x_49; 
lean::dec(x_26);
x_46 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_48 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(x_0, x_1, x_46);
x_49 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_48, x_33);
return x_49;
}
else
{
uint32 x_51; obj* x_53; obj* x_54; 
lean::dec(x_5);
x_51 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_53 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(x_0, x_1, x_51);
x_54 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_53, x_33);
return x_54;
}
}
}
else
{
uint32 x_56; obj* x_58; obj* x_59; 
lean::dec(x_5);
x_56 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_58 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(x_0, x_1, x_56);
x_59 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_58, x_33);
return x_59;
}
}
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
obj* x_7; obj* x_9; obj* x_10; uint8 x_11; uint32 x_13; 
x_9 = lean::mk_nat_obj(92u);
x_10 = lean::mk_nat_obj(55296u);
x_11 = lean::nat_dec_lt(x_9, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::mk_nat_obj(57343u);
x_16 = lean::nat_dec_lt(x_15, x_9);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_19; uint32 x_20; 
lean::dec(x_9);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_13 = x_20;
goto lbl_14;
}
else
{
obj* x_22; uint8 x_23; 
x_22 = lean::mk_nat_obj(1114112u);
x_23 = lean::nat_dec_lt(x_9, x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_26; uint32 x_27; 
lean::dec(x_9);
x_26 = lean::mk_nat_obj(0u);
x_27 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_13 = x_27;
goto lbl_14;
}
else
{
uint32 x_29; 
x_29 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_13 = x_29;
goto lbl_14;
}
}
}
else
{
uint32 x_31; 
x_31 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_13 = x_31;
goto lbl_14;
}
lbl_8:
{
obj* x_34; obj* x_35; uint8 x_36; uint32 x_38; 
lean::dec(x_7);
x_34 = lean::mk_nat_obj(34u);
x_35 = lean::mk_nat_obj(55296u);
x_36 = lean::nat_dec_lt(x_34, x_35);
lean::dec(x_35);
if (x_36 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = lean::mk_nat_obj(57343u);
x_41 = lean::nat_dec_lt(x_40, x_34);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_44; uint32 x_45; 
lean::dec(x_34);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::unbox_uint32(x_44);
lean::dec(x_44);
x_38 = x_45;
goto lbl_39;
}
else
{
obj* x_47; uint8 x_48; 
x_47 = lean::mk_nat_obj(1114112u);
x_48 = lean::nat_dec_lt(x_34, x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_51; uint32 x_52; 
lean::dec(x_34);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::unbox_uint32(x_51);
lean::dec(x_51);
x_38 = x_52;
goto lbl_39;
}
else
{
uint32 x_54; 
x_54 = lean::unbox_uint32(x_34);
lean::dec(x_34);
x_38 = x_54;
goto lbl_39;
}
}
}
else
{
uint32 x_56; 
x_56 = lean::unbox_uint32(x_34);
lean::dec(x_34);
x_38 = x_56;
goto lbl_39;
}
lbl_39:
{
obj* x_58; obj* x_59; uint8 x_60; 
x_58 = lean::box_uint32(x_6);
x_59 = lean::box_uint32(x_38);
x_60 = lean::nat_dec_eq(x_58, x_59);
lean::dec(x_59);
lean::dec(x_58);
if (x_60 == 0)
{
obj* x_63; obj* x_64; 
x_63 = lean::string_push(x_0, x_6);
x_64 = l_lean_parser_parse__string__literal__aux___main___rarg(x_1, x_2, x_3, x_4, x_63);
return x_64;
}
else
{
obj* x_68; obj* x_71; obj* x_74; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_68 = lean::cnstr_get(x_3, 0);
lean::inc(x_68);
lean::dec(x_3);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
x_74 = lean::apply_2(x_71, lean::box(0), x_0);
return x_74;
}
}
}
lbl_14:
{
obj* x_75; obj* x_76; uint8 x_77; 
x_75 = lean::box_uint32(x_6);
x_76 = lean::box_uint32(x_13);
x_77 = lean::nat_dec_eq(x_75, x_76);
lean::dec(x_76);
lean::dec(x_75);
if (x_77 == 0)
{
obj* x_81; 
lean::dec(x_5);
x_81 = lean::box(0);
x_7 = x_81;
goto lbl_8;
}
else
{
obj* x_85; obj* x_86; obj* x_87; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_85 = l_lean_parser_parse__quoted__char___rarg(x_1, x_2, x_3);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal__aux___main___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_86, 0, x_0);
lean::closure_set(x_86, 1, x_1);
lean::closure_set(x_86, 2, x_2);
lean::closure_set(x_86, 3, x_3);
lean::closure_set(x_86, 4, x_4);
x_87 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_85, x_86);
return x_87;
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__1___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__4___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__7___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal__aux___main___spec__10___rarg(x_0, x_1, x_3);
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__3___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__6___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__9___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
uint32 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_3);
x_24 = l_char_quote__core(x_16);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_parse__string__literal___spec__12___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_4);
lean::closure_set(x_36, 1, x_17);
x_37 = lean::apply_2(x_3, lean::box(0), x_36);
return x_37;
}
}
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
obj* l_lean_parser_parse__string__literal___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; uint8 x_7; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::mk_nat_obj(34u);
x_6 = lean::mk_nat_obj(55296u);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
if (x_7 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::mk_nat_obj(57343u);
x_14 = lean::nat_dec_lt(x_13, x_5);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_17; uint32 x_18; obj* x_20; obj* x_21; 
lean::dec(x_5);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::unbox_uint32(x_17);
lean::dec(x_17);
x_20 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(x_0, x_1, x_18);
x_21 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_20, x_12);
return x_21;
}
else
{
obj* x_22; uint8 x_23; 
x_22 = lean::mk_nat_obj(1114112u);
x_23 = lean::nat_dec_lt(x_5, x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_26; uint32 x_27; obj* x_29; obj* x_30; 
lean::dec(x_5);
x_26 = lean::mk_nat_obj(0u);
x_27 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_29 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(x_0, x_1, x_27);
x_30 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_29, x_12);
return x_30;
}
else
{
uint32 x_31; obj* x_33; obj* x_34; 
x_31 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_33 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(x_0, x_1, x_31);
x_34 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_33, x_12);
return x_34;
}
}
}
else
{
uint32 x_35; obj* x_37; obj* x_38; 
x_35 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_37 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(x_0, x_1, x_35);
x_38 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_37, x_12);
return x_38;
}
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__1___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__4___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__7___rarg(x_0, x_1, x_3);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_parse__string__literal___spec__10___rarg(x_0, x_1, x_3);
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
 l_lean_parser_parse__hex__digit___rarg___closed__1 = _init_l_lean_parser_parse__hex__digit___rarg___closed__1();
 l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1 = _init_l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1();
}
