// Lean compiler output
// Module: init.lean.parser.identifier
// Imports: init.data.char.basic init.lean.parser.parsec
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
obj* l_lean_parser_cpp__identifier___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___boxed(obj*);
obj* l_lean_is__greek___boxed(obj*);
uint8 l_lean_is__letter__like(uint32);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3;
obj* l_lean_parser_monad__parsec_curr___rarg(obj*, obj*);
obj* l_lean_parser_identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3(obj*, obj*, obj*);
uint32 l_lean_id__end__escape;
obj* l_lean_parser_id__part__default___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2(obj*, obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_c__identifier(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_lean_is__id__end__escape(uint32);
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_is__id__end__escape___boxed(obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_id__begin__escape___boxed;
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___boxed(obj*, obj*, obj*);
uint8 l_string_is__empty(obj*);
uint8 l_lean_is__sub__script__alnum(uint32);
uint8 l_char_is__alpha(uint32);
namespace lean {
uint32 string_iterator_curr(obj*);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1(obj*, obj*);
obj* l_lean_is__id__rest___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4(obj*);
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1;
obj* l_lean_parser_id__part__escaped___boxed(obj*, obj*);
obj* l_lean_parser_c__identifier___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed(obj*, obj*);
obj* l_lean_is__letter__like___boxed(obj*);
obj* l_lean_parser_id__part__default___rarg(obj*, obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___boxed(obj*, obj*, obj*);
obj* l_string_append___boxed(obj*, obj*);
uint8 l_lean_is__greek(uint32);
obj* l_lean_parser_c__identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_is__id__first___boxed(obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_parser_c__identifier___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2(obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_c__identifier___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_id__part___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_id__end__escape___boxed;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___boxed(obj*);
obj* l_lean_is__sub__script__alnum___boxed(obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part__default___boxed(obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1(obj*, obj*);
uint32 l_lean_id__begin__escape;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_is__id__begin__escape___boxed(obj*);
obj* l_lean_parser_id__part__default___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_cond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_c__identifier___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_id__part__default(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg(obj*, uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_id__part__default___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part(obj*, obj*);
obj* l_lean_parser_id__part___rarg(obj*, obj*, obj*);
namespace lean {
obj* string_iterator_remaining(obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5(obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___boxed(obj*, obj*);
uint8 l_char_is__alphanum(uint32);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_parser_identifier___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2(obj*, obj*, obj*);
uint8 l_lean_is__id__first(uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___rarg(obj*, obj*, uint32);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg(obj*, uint32);
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4(obj*, obj*, obj*);
uint8 l_lean_is__id__begin__escape(uint32);
extern obj* l_lean_parser_monad__parsec_try___rarg___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___boxed(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5(obj*);
obj* l_lean_parser_identifier___rarg___closed__1;
obj* l_lean_parser_monad__parsec_str__core___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_cpp__identifier(obj*, obj*);
obj* l_lean_parser_id__part___rarg___closed__1;
obj* l_lean_parser_c__identifier___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__greek(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = 913;
x_2 = x_1 <= x_0;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint32 x_4; uint8 x_5; 
x_4 = 989;
x_5 = x_0 <= x_4;
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_lean_is__greek___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__greek(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_is__letter__like(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; uint8 x_4; uint8 x_6; uint8 x_8; uint8 x_10; uint8 x_12; uint8 x_14; 
x_1 = 945;
x_14 = x_1 <= x_0;
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
x_12 = x_15;
goto lbl_13;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = 969;
x_17 = x_0 <= x_16;
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 0;
x_12 = x_18;
goto lbl_13;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = 955;
x_20 = x_0 == x_19;
if (x_20 == 0)
{
uint8 x_21; 
x_21 = 1;
x_12 = x_21;
goto lbl_13;
}
else
{
uint8 x_22; 
x_22 = 0;
x_12 = x_22;
goto lbl_13;
}
}
}
lbl_3:
{
uint32 x_23; uint8 x_24; 
x_23 = 119964;
x_24 = x_23 <= x_0;
if (x_24 == 0)
{
if (x_2 == 0)
{
return x_2;
}
else
{
return x_2;
}
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = 120223;
x_26 = x_0 <= x_25;
if (x_26 == 0)
{
return x_2;
}
else
{
uint8 x_27; 
x_27 = 1;
return x_27;
}
}
}
lbl_5:
{
uint32 x_28; uint8 x_29; 
x_28 = 8448;
x_29 = x_28 <= x_0;
if (x_29 == 0)
{
if (x_4 == 0)
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
else
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
}
else
{
uint32 x_30; uint8 x_31; 
x_30 = 8527;
x_31 = x_0 <= x_30;
if (x_31 == 0)
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
else
{
uint8 x_32; 
x_32 = 1;
return x_32;
}
}
}
lbl_7:
{
uint32 x_33; uint8 x_34; 
x_33 = 7936;
x_34 = x_33 <= x_0;
if (x_34 == 0)
{
if (x_6 == 0)
{
if (x_6 == 0)
{
x_4 = x_6;
goto lbl_5;
}
else
{
if (x_6 == 0)
{
x_2 = x_6;
goto lbl_3;
}
else
{
return x_6;
}
}
}
else
{
if (x_6 == 0)
{
x_4 = x_6;
goto lbl_5;
}
else
{
if (x_6 == 0)
{
x_2 = x_6;
goto lbl_3;
}
else
{
return x_6;
}
}
}
}
else
{
uint32 x_35; uint8 x_36; 
x_35 = 8190;
x_36 = x_0 <= x_35;
if (x_36 == 0)
{
if (x_6 == 0)
{
x_4 = x_6;
goto lbl_5;
}
else
{
if (x_6 == 0)
{
x_2 = x_6;
goto lbl_3;
}
else
{
return x_6;
}
}
}
else
{
uint8 x_37; 
x_37 = 1;
return x_37;
}
}
}
lbl_9:
{
uint32 x_38; uint8 x_39; 
x_38 = 970;
x_39 = x_38 <= x_0;
if (x_39 == 0)
{
if (x_8 == 0)
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
if (x_8 == 0)
{
x_4 = x_8;
goto lbl_5;
}
else
{
if (x_8 == 0)
{
x_2 = x_8;
goto lbl_3;
}
else
{
return x_8;
}
}
}
}
else
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
if (x_8 == 0)
{
x_4 = x_8;
goto lbl_5;
}
else
{
if (x_8 == 0)
{
x_2 = x_8;
goto lbl_3;
}
else
{
return x_8;
}
}
}
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = 1019;
x_41 = x_0 <= x_40;
if (x_41 == 0)
{
if (x_8 == 0)
{
x_6 = x_8;
goto lbl_7;
}
else
{
if (x_8 == 0)
{
x_4 = x_8;
goto lbl_5;
}
else
{
if (x_8 == 0)
{
x_2 = x_8;
goto lbl_3;
}
else
{
return x_8;
}
}
}
}
else
{
uint8 x_42; 
x_42 = 1;
return x_42;
}
}
}
lbl_11:
{
if (x_10 == 0)
{
x_6 = x_10;
goto lbl_7;
}
else
{
if (x_10 == 0)
{
x_4 = x_10;
goto lbl_5;
}
else
{
if (x_10 == 0)
{
x_2 = x_10;
goto lbl_3;
}
else
{
return x_10;
}
}
}
}
lbl_13:
{
uint8 x_43; uint8 x_45; 
if (x_12 == 0)
{
uint32 x_47; uint8 x_48; 
x_47 = 913;
x_48 = x_47 <= x_0;
if (x_48 == 0)
{
if (x_12 == 0)
{
if (x_12 == 0)
{
x_43 = x_12;
goto lbl_44;
}
else
{
x_45 = x_12;
goto lbl_46;
}
}
else
{
if (x_12 == 0)
{
x_43 = x_12;
goto lbl_44;
}
else
{
x_45 = x_12;
goto lbl_46;
}
}
}
else
{
uint32 x_49; uint8 x_50; 
x_49 = 937;
x_50 = x_0 <= x_49;
if (x_50 == 0)
{
if (x_12 == 0)
{
x_43 = x_12;
goto lbl_44;
}
else
{
x_45 = x_12;
goto lbl_46;
}
}
else
{
uint8 x_51; 
x_51 = 1;
x_45 = x_51;
goto lbl_46;
}
}
}
else
{
if (x_12 == 0)
{
x_8 = x_12;
goto lbl_9;
}
else
{
x_10 = x_12;
goto lbl_11;
}
}
lbl_44:
{
if (x_43 == 0)
{
if (x_43 == 0)
{
x_8 = x_43;
goto lbl_9;
}
else
{
x_10 = x_43;
goto lbl_11;
}
}
else
{
uint32 x_52; uint8 x_53; 
x_52 = 931;
x_53 = x_0 == x_52;
if (x_53 == 0)
{
if (x_43 == 0)
{
x_8 = x_43;
goto lbl_9;
}
else
{
x_10 = x_43;
goto lbl_11;
}
}
else
{
if (x_12 == 0)
{
x_8 = x_12;
goto lbl_9;
}
else
{
x_10 = x_12;
goto lbl_11;
}
}
}
}
lbl_46:
{
uint32 x_54; uint8 x_55; 
x_54 = 928;
x_55 = x_0 == x_54;
if (x_55 == 0)
{
if (x_45 == 0)
{
if (x_45 == 0)
{
x_8 = x_45;
goto lbl_9;
}
else
{
x_10 = x_45;
goto lbl_11;
}
}
else
{
uint32 x_56; uint8 x_57; 
x_56 = 931;
x_57 = x_0 == x_56;
if (x_57 == 0)
{
if (x_45 == 0)
{
x_8 = x_45;
goto lbl_9;
}
else
{
x_10 = x_45;
goto lbl_11;
}
}
else
{
if (x_12 == 0)
{
x_8 = x_12;
goto lbl_9;
}
else
{
x_10 = x_12;
goto lbl_11;
}
}
}
}
else
{
if (x_12 == 0)
{
if (x_12 == 0)
{
x_8 = x_12;
goto lbl_9;
}
else
{
x_10 = x_12;
goto lbl_11;
}
}
else
{
if (x_12 == 0)
{
x_8 = x_12;
goto lbl_9;
}
else
{
x_10 = x_12;
goto lbl_11;
}
}
}
}
}
}
}
obj* l_lean_is__letter__like___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__letter__like(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_is__sub__script__alnum(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; uint8 x_4; uint8 x_6; 
x_1 = 8319;
x_6 = x_1 <= x_0;
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
x_4 = x_7;
goto lbl_5;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = 8329;
x_9 = x_0 <= x_8;
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
x_4 = x_10;
goto lbl_5;
}
else
{
uint8 x_11; 
x_11 = 1;
return x_11;
}
}
lbl_3:
{
uint32 x_12; uint8 x_13; 
x_12 = 7522;
x_13 = x_12 <= x_0;
if (x_13 == 0)
{
if (x_2 == 0)
{
return x_2;
}
else
{
return x_2;
}
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 7530;
x_15 = x_0 <= x_14;
if (x_15 == 0)
{
return x_2;
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
}
lbl_5:
{
uint32 x_17; uint8 x_18; 
x_17 = 8336;
x_18 = x_17 <= x_0;
if (x_18 == 0)
{
if (x_4 == 0)
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
else
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = 8348;
x_20 = x_0 <= x_19;
if (x_20 == 0)
{
if (x_4 == 0)
{
x_2 = x_4;
goto lbl_3;
}
else
{
return x_4;
}
}
else
{
uint8 x_21; 
x_21 = 1;
return x_21;
}
}
}
}
}
obj* l_lean_is__sub__script__alnum___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__sub__script__alnum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_is__id__first(uint32 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_char_is__alpha(x_0);
if (x_1 == 0)
{
uint32 x_2; uint8 x_3; 
x_2 = 95;
x_3 = x_0 == x_2;
if (x_3 == 0)
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = l_lean_is__letter__like(x_0);
return x_4;
}
else
{
return x_1;
}
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
else
{
if (x_1 == 0)
{
uint8 x_6; 
x_6 = l_lean_is__letter__like(x_0);
return x_6;
}
else
{
return x_1;
}
}
}
}
obj* l_lean_is__id__first___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__id__first(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_is__id__rest(uint32 x_0) {
_start:
{
uint8 x_1; uint8 x_3; 
x_3 = l_char_is__alphanum(x_0);
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 95;
x_5 = x_0 == x_4;
if (x_5 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
uint8 x_6; 
x_6 = l_lean_is__letter__like(x_0);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = l_lean_is__sub__script__alnum(x_0);
return x_7;
}
else
{
return x_6;
}
}
else
{
if (x_3 == 0)
{
uint8 x_8; 
x_8 = l_lean_is__sub__script__alnum(x_0);
return x_8;
}
else
{
return x_3;
}
}
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
else
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
uint8 x_10; 
x_10 = l_lean_is__letter__like(x_0);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = l_lean_is__sub__script__alnum(x_0);
return x_11;
}
else
{
return x_10;
}
}
else
{
if (x_3 == 0)
{
uint8 x_12; 
x_12 = l_lean_is__sub__script__alnum(x_0);
return x_12;
}
else
{
return x_3;
}
}
}
}
lbl_2:
{
uint32 x_13; uint8 x_14; 
x_13 = 39;
x_14 = x_0 == x_13;
if (x_14 == 0)
{
if (x_1 == 0)
{
uint8 x_15; 
x_15 = l_lean_is__letter__like(x_0);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = l_lean_is__sub__script__alnum(x_0);
return x_16;
}
else
{
return x_15;
}
}
else
{
if (x_1 == 0)
{
uint8 x_17; 
x_17 = l_lean_is__sub__script__alnum(x_0);
return x_17;
}
else
{
return x_1;
}
}
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
}
}
obj* l_lean_is__id__rest___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__id__rest(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint32 _init_l_lean_id__begin__escape() {
_start:
{
uint32 x_0; 
x_0 = 171;
return x_0;
}
}
obj* _init_l_lean_id__begin__escape___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_lean_id__begin__escape;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint32 _init_l_lean_id__end__escape() {
_start:
{
uint32 x_0; 
x_0 = 187;
return x_0;
}
}
obj* _init_l_lean_id__end__escape___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_lean_id__end__escape;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint8 l_lean_is__id__begin__escape(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_lean_id__begin__escape;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_lean_is__id__begin__escape___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__id__begin__escape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_is__id__end__escape(uint32 x_0) {
_start:
{
uint32 x_1; uint8 x_2; 
x_1 = l_lean_id__end__escape;
x_2 = x_0 == x_1;
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_lean_is__id__end__escape___boxed(obj* x_0) {
_start:
{
uint32 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_lean_is__id__end__escape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_lean_parser_id__part__default___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(x_1, lean::box(0), x_8, x_9, x_7, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = lean::string_iterator_curr(x_3);
x_12 = l_lean_is__id__first(x_11);
if (x_12 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_3);
lean::dec(x_2);
x_15 = l_char_quote__core(x_11);
x_16 = l_char_has__repr___closed__1;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_19 = lean::string_append(x_17, x_16);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
x_22 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(x_1, lean::box(0), x_19, x_21, x_20, x_20);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
x_24 = lean::box_uint32(x_11);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_25, 0, x_3);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::apply_2(x_2, lean::box(0), x_25);
return x_26;
}
}
}
}
obj* l_lean_parser_id__part__default___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__default___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_5);
lean::inc(x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed), 2, 1);
lean::closure_set(x_14, 0, x_1);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_lean_parser_id__part__default(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__default___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__default___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_id__part__default___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_id__part__default___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_parser_id__part__default___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_id__part__default___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_id__part__default___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_id__part__default(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(x_1, lean::box(0), x_8, x_9, x_7, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = lean::string_iterator_curr(x_3);
x_12 = l_lean_is__id__end__escape(x_11);
if (x_12 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_14 = lean::box_uint32(x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_15, 0, x_3);
lean::closure_set(x_15, 1, x_14);
x_16 = lean::apply_2(x_2, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_3);
lean::dec(x_2);
x_19 = l_char_quote__core(x_11);
x_20 = l_char_has__repr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(x_1, lean::box(0), x_23, x_25, x_24, x_24);
return x_26;
}
}
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_4);
x_8 = lean::apply_2(x_4, lean::box(0), x_6);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
lean::inc(x_2);
x_12 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_8, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed), 2, 1);
lean::closure_set(x_13, 0, x_1);
x_14 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_id__part__escaped___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; uint32 x_11; obj* x_14; obj* x_17; obj* x_18; uint32 x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 4);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_lean_id__begin__escape;
lean::inc(x_1);
lean::inc(x_0);
x_14 = l_lean_parser_monad__parsec_ch___rarg(x_0, x_1, x_11);
lean::inc(x_1);
lean::inc(x_0);
x_17 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(x_0, x_1);
x_18 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_14, x_17);
x_19 = l_lean_id__end__escape;
x_20 = l_lean_parser_monad__parsec_ch___rarg(x_0, x_1, x_19);
x_21 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_18, x_20);
return x_21;
}
}
obj* l_lean_parser_id__part__escaped(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__escaped___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_id__part__escaped___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_id__part__escaped(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_id__part___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_is__id__begin__escape___boxed), 1, 0);
return x_0;
}
}
obj* l_lean_parser_id__part___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = l_lean_parser_id__part__escaped___rarg(x_0, x_1, x_2);
lean::inc(x_1);
lean::inc(x_0);
x_9 = l_lean_parser_id__part__default___rarg(x_0, x_1, x_2);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_parser_monad__parsec_curr___rarg(x_0, x_1);
x_22 = l_lean_parser_id__part___rarg___closed__1;
x_23 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_22, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_cond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_6);
x_25 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
obj* l_lean_parser_id__part(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_id__part___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_id__part(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_12; obj* x_13; obj* x_15; uint32 x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_33; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_12 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 4);
lean::inc(x_15);
x_17 = 46;
lean::inc(x_1);
lean::inc(x_0);
x_20 = l_lean_parser_monad__parsec_ch___rarg(x_0, x_1, x_17);
x_21 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_20, x_12);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::inc(x_3);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_27, 0, x_3);
lean::closure_set(x_27, 1, x_0);
lean::closure_set(x_27, 2, x_1);
lean::closure_set(x_27, 3, x_2);
lean::closure_set(x_27, 4, x_8);
x_28 = lean::apply_4(x_24, lean::box(0), lean::box(0), x_21, x_27);
x_29 = lean::cnstr_get(x_13, 1);
lean::inc(x_29);
lean::dec(x_13);
x_32 = lean::apply_2(x_29, lean::box(0), x_3);
x_33 = lean::apply_3(x_22, lean::box(0), x_28, x_32);
return x_33;
}
else
{
obj* x_36; obj* x_39; obj* x_42; 
lean::dec(x_1);
lean::dec(x_0);
x_36 = lean::cnstr_get(x_2, 0);
lean::inc(x_36);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = lean::apply_2(x_39, lean::box(0), x_3);
return x_42;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::string_iterator_remaining(x_4);
x_6 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* _init_l_lean_parser_identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_2);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_12);
x_17 = lean::apply_3(x_12, lean::box(0), x_15, x_11);
x_18 = l_lean_parser_identifier___rarg___closed__1;
x_19 = lean::apply_3(x_12, lean::box(0), x_18, x_17);
return x_19;
}
}
obj* l_lean_parser_identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_identifier___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_identifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_identifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_10; obj* x_11; uint32 x_13; uint8 x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_14 = l_char_is__alphanum(x_13);
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 95;
x_16 = x_13 == x_15;
if (x_16 == 0)
{
if (x_14 == 0)
{
obj* x_18; 
lean::dec(x_11);
x_18 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_18;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::string_push(x_1, x_13);
x_22 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_21;
x_2 = x_22;
goto _start;
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::string_push(x_1, x_13);
x_25 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_24;
x_2 = x_25;
goto _start;
}
}
else
{
if (x_14 == 0)
{
obj* x_28; 
lean::dec(x_11);
x_28 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_28;
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::string_push(x_1, x_13);
x_32 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_31;
x_2 = x_32;
goto _start;
}
}
}
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_35;
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_lean_parser_c__identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(x_1, lean::box(0), x_8, x_9, x_7, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = lean::string_iterator_curr(x_3);
x_12 = l_char_is__alpha(x_11);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 95;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
if (x_12 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_3);
lean::dec(x_2);
x_17 = l_char_quote__core(x_11);
x_18 = l_char_has__repr___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = lean::string_append(x_19, x_18);
x_22 = lean::box(0);
x_23 = l_mjoin___rarg___closed__1;
x_24 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(x_1, lean::box(0), x_21, x_23, x_22, x_22);
return x_24;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_26 = lean::box_uint32(x_11);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_27, 0, x_3);
lean::closure_set(x_27, 1, x_26);
x_28 = lean::apply_2(x_2, lean::box(0), x_27);
return x_28;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_30 = lean::box_uint32(x_11);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_31, 0, x_3);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::apply_2(x_2, lean::box(0), x_31);
return x_32;
}
}
else
{
if (x_12 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_3);
lean::dec(x_2);
x_35 = l_char_quote__core(x_11);
x_36 = l_char_has__repr___closed__1;
x_37 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_39 = lean::string_append(x_37, x_36);
x_40 = lean::box(0);
x_41 = l_mjoin___rarg___closed__1;
x_42 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg(x_1, lean::box(0), x_39, x_41, x_40, x_40);
return x_42;
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
x_44 = lean::box_uint32(x_11);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_45, 0, x_3);
lean::closure_set(x_45, 1, x_44);
x_46 = lean::apply_2(x_2, lean::box(0), x_45);
return x_46;
}
}
}
}
}
obj* _init_l_lean_parser_c__identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_c__identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_c__identifier___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_5);
lean::inc(x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___boxed), 2, 1);
lean::closure_set(x_15, 0, x_1);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_13, x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::dec(x_1);
x_20 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_17);
x_22 = lean::apply_3(x_17, lean::box(0), x_20, x_16);
x_23 = l_lean_parser_c__identifier___rarg___closed__1;
x_24 = lean::apply_3(x_17, lean::box(0), x_23, x_22);
return x_24;
}
}
obj* l_lean_parser_c__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_c__identifier___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_c__identifier___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___rarg(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_c__identifier___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_c__identifier___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_parser_c__identifier___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_c__identifier___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_c__identifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_c__identifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_string_is__empty(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_str__core___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_string_join___closed__1;
x_21 = lean::apply_2(x_17, lean::box(0), x_20);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_2);
x_9 = l_string_join___closed__1;
x_10 = l_list_foldl___main___at_string_join___spec__1(x_9, x_8);
lean::dec(x_8);
x_12 = lean::apply_2(x_3, lean::box(0), x_10);
return x_12;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("::");
return x_0;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("::");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_append___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_15 = l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1;
x_16 = l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2;
lean::inc(x_2);
lean::inc(x_1);
x_19 = l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(x_1, x_2, x_15, x_16);
x_20 = l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3;
x_21 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_20, x_19);
x_22 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_21, x_3);
x_23 = l_lean_parser_monad__parsec_many___rarg(x_1, x_2, lean::box(0), x_0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_6);
lean::closure_set(x_24, 1, x_5);
x_25 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C++ identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_cpp__identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_lean_parser_c__identifier___rarg(x_0, x_1, x_2);
lean::inc(x_3);
lean::inc(x_7);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg___lambda__2), 6, 5);
lean::closure_set(x_11, 0, x_2);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_1);
lean::closure_set(x_11, 3, x_7);
lean::closure_set(x_11, 4, x_3);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_7, x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_13);
x_18 = lean::apply_3(x_13, lean::box(0), x_16, x_12);
x_19 = l_lean_parser_cpp__identifier___rarg___closed__1;
x_20 = lean::apply_3(x_13, lean::box(0), x_19, x_18);
return x_20;
}
}
obj* l_lean_parser_cpp__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_cpp__identifier___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_cpp__identifier___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_cpp__identifier(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
void initialize_init_data_char_basic();
void initialize_init_lean_parser_parsec();
static bool _G_initialized = false;
void initialize_init_lean_parser_identifier() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_char_basic();
 initialize_init_lean_parser_parsec();
 l_lean_id__begin__escape = _init_l_lean_id__begin__escape();
 l_lean_id__begin__escape___boxed = _init_l_lean_id__begin__escape___boxed();
lean::mark_persistent(l_lean_id__begin__escape___boxed);
 l_lean_id__end__escape = _init_l_lean_id__end__escape();
 l_lean_id__end__escape___boxed = _init_l_lean_id__end__escape___boxed();
lean::mark_persistent(l_lean_id__end__escape___boxed);
 l_lean_parser_id__part___rarg___closed__1 = _init_l_lean_parser_id__part___rarg___closed__1();
lean::mark_persistent(l_lean_parser_id__part___rarg___closed__1);
 l_lean_parser_identifier___rarg___closed__1 = _init_l_lean_parser_identifier___rarg___closed__1();
lean::mark_persistent(l_lean_parser_identifier___rarg___closed__1);
 l_lean_parser_c__identifier___rarg___closed__1 = _init_l_lean_parser_c__identifier___rarg___closed__1();
lean::mark_persistent(l_lean_parser_c__identifier___rarg___closed__1);
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1);
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2();
lean::mark_persistent(l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2);
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3();
lean::mark_persistent(l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3);
 l_lean_parser_cpp__identifier___rarg___closed__1 = _init_l_lean_parser_cpp__identifier___rarg___closed__1();
lean::mark_persistent(l_lean_parser_cpp__identifier___rarg___closed__1);
}
