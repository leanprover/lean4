// Lean compiler output
// Module: init.lean.parser.identifier
// Imports: init.data.char.basic init.lean.parser.parsec
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
obj* l___private_2142412293__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg(obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_is__greek___boxed(obj*);
uint8 l_lean_is__letter__like(uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9(obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3;
obj* l_lean_parser_monad__parsec_curr___rarg(obj*, obj*);
obj* l_lean_parser_identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier(obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3(obj*, obj*, obj*);
obj* l_lean_id__end__escape;
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_labels___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg(obj*, obj*, uint32);
obj* l_lean_parser_cpp__identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg(obj*, uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg(obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_c__identifier(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed(obj*, obj*);
uint8 l_lean_is__id__end__escape(uint32);
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_is__id__end__escape___boxed(obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg(obj*, obj*, uint32);
uint8 l_string_is__empty(obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg(obj*, obj*, obj*, obj*);
uint8 l_lean_is__sub__script__alnum(uint32);
uint8 l_char_is__alpha(uint32);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_is__id__rest___boxed(obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_c__identifier___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed(obj*, obj*);
obj* l_lean_is__letter__like___boxed(obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part__default___rarg(obj*, obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__greek(uint32);
obj* l_lean_parser_c__identifier___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_is__id__first___boxed(obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg(obj*, uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_c__identifier___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2(obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_is__sub__script__alnum___boxed(obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_id__begin__escape;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5(obj*);
obj* l_lean_is__id__begin__escape___boxed(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_id__part__default___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_cond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_id__part__default(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg(obj*, uint32);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_id__part(obj*, obj*);
obj* l_lean_parser_id__part___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_char_is__alphanum(uint32);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2(obj*, obj*, obj*);
uint8 l_lean_is__id__first(uint32);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___rarg(obj*, obj*, uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4(obj*, obj*, obj*);
uint8 l_lean_is__id__begin__escape(uint32);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5(obj*, obj*);
extern obj* l_lean_parser_monad__parsec_try___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1(obj*, obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_cpp__identifier___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_identifier___rarg___closed__1;
obj* l_char_quote__core(uint32);
obj* l_lean_parser_cpp__identifier(obj*, obj*);
obj* l_lean_parser_id__part___rarg___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__greek(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::mk_nat_obj(913u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(989u);
x_8 = lean::nat_dec_le(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
if (x_8 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
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
uint8 x_1; uint8 x_3; uint8 x_5; uint8 x_7; uint8 x_9; uint8 x_11; obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::mk_nat_obj(945u);
x_14 = lean::box_uint32(x_0);
x_15 = lean::nat_dec_le(x_13, x_14);
lean::dec(x_13);
if (x_15 == 0)
{
uint8 x_18; 
lean::dec(x_14);
x_18 = 0;
x_11 = x_18;
goto lbl_12;
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::mk_nat_obj(969u);
x_20 = lean::nat_dec_le(x_14, x_19);
lean::dec(x_19);
if (x_20 == 0)
{
uint8 x_23; 
lean::dec(x_14);
x_23 = 0;
x_11 = x_23;
goto lbl_12;
}
else
{
obj* x_24; uint8 x_25; 
x_24 = lean::mk_nat_obj(955u);
x_25 = lean::nat_dec_eq(x_14, x_24);
lean::dec(x_24);
lean::dec(x_14);
if (x_25 == 0)
{
uint8 x_28; 
x_28 = 1;
x_11 = x_28;
goto lbl_12;
}
else
{
uint8 x_29; 
x_29 = 0;
x_11 = x_29;
goto lbl_12;
}
}
}
lbl_2:
{
obj* x_30; obj* x_31; uint8 x_32; 
x_30 = lean::mk_nat_obj(119964u);
x_31 = lean::box_uint32(x_0);
x_32 = lean::nat_dec_le(x_30, x_31);
lean::dec(x_30);
if (x_32 == 0)
{
lean::dec(x_31);
return x_1;
}
else
{
obj* x_35; uint8 x_36; 
x_35 = lean::mk_nat_obj(120223u);
x_36 = lean::nat_dec_le(x_31, x_35);
lean::dec(x_35);
lean::dec(x_31);
if (x_36 == 0)
{
return x_1;
}
else
{
uint8 x_39; 
x_39 = 1;
return x_39;
}
}
}
lbl_4:
{
obj* x_40; obj* x_41; uint8 x_42; 
x_40 = lean::mk_nat_obj(8448u);
x_41 = lean::box_uint32(x_0);
x_42 = lean::nat_dec_le(x_40, x_41);
lean::dec(x_40);
if (x_42 == 0)
{
lean::dec(x_41);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
obj* x_45; uint8 x_46; 
x_45 = lean::mk_nat_obj(8527u);
x_46 = lean::nat_dec_le(x_41, x_45);
lean::dec(x_45);
lean::dec(x_41);
if (x_46 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
uint8 x_49; 
x_49 = 1;
return x_49;
}
}
}
lbl_6:
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = lean::mk_nat_obj(7936u);
x_51 = lean::box_uint32(x_0);
x_52 = lean::nat_dec_le(x_50, x_51);
lean::dec(x_50);
if (x_52 == 0)
{
lean::dec(x_51);
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
obj* x_55; uint8 x_56; 
x_55 = lean::mk_nat_obj(8190u);
x_56 = lean::nat_dec_le(x_51, x_55);
lean::dec(x_55);
lean::dec(x_51);
if (x_56 == 0)
{
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
uint8 x_59; 
x_59 = 1;
return x_59;
}
}
}
lbl_8:
{
obj* x_60; obj* x_61; uint8 x_62; 
x_60 = lean::mk_nat_obj(970u);
x_61 = lean::box_uint32(x_0);
x_62 = lean::nat_dec_le(x_60, x_61);
lean::dec(x_60);
if (x_62 == 0)
{
lean::dec(x_61);
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(1019u);
x_66 = lean::nat_dec_le(x_61, x_65);
lean::dec(x_65);
lean::dec(x_61);
if (x_66 == 0)
{
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
uint8 x_69; 
x_69 = 1;
return x_69;
}
}
}
lbl_10:
{
if (x_9 == 0)
{
x_5 = x_9;
goto lbl_6;
}
else
{
if (x_9 == 0)
{
x_3 = x_9;
goto lbl_4;
}
else
{
if (x_9 == 0)
{
x_1 = x_9;
goto lbl_2;
}
else
{
return x_9;
}
}
}
}
lbl_12:
{
uint8 x_70; uint8 x_72; 
if (x_11 == 0)
{
obj* x_74; obj* x_75; uint8 x_76; 
x_74 = lean::mk_nat_obj(913u);
x_75 = lean::box_uint32(x_0);
x_76 = lean::nat_dec_le(x_74, x_75);
lean::dec(x_74);
if (x_76 == 0)
{
lean::dec(x_75);
if (x_11 == 0)
{
x_70 = x_11;
goto lbl_71;
}
else
{
x_72 = x_11;
goto lbl_73;
}
}
else
{
obj* x_79; uint8 x_80; 
x_79 = lean::mk_nat_obj(937u);
x_80 = lean::nat_dec_le(x_75, x_79);
lean::dec(x_79);
lean::dec(x_75);
if (x_80 == 0)
{
if (x_11 == 0)
{
x_70 = x_11;
goto lbl_71;
}
else
{
x_72 = x_11;
goto lbl_73;
}
}
else
{
uint8 x_83; 
x_83 = 1;
x_72 = x_83;
goto lbl_73;
}
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
lbl_71:
{
if (x_70 == 0)
{
if (x_70 == 0)
{
x_7 = x_70;
goto lbl_8;
}
else
{
x_9 = x_70;
goto lbl_10;
}
}
else
{
obj* x_84; obj* x_85; uint8 x_86; 
x_84 = lean::mk_nat_obj(931u);
x_85 = lean::box_uint32(x_0);
x_86 = lean::nat_dec_eq(x_85, x_84);
lean::dec(x_84);
lean::dec(x_85);
if (x_86 == 0)
{
if (x_70 == 0)
{
x_7 = x_70;
goto lbl_8;
}
else
{
x_9 = x_70;
goto lbl_10;
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
}
lbl_73:
{
obj* x_89; obj* x_90; uint8 x_91; 
x_89 = lean::mk_nat_obj(928u);
x_90 = lean::box_uint32(x_0);
x_91 = lean::nat_dec_eq(x_90, x_89);
lean::dec(x_89);
if (x_91 == 0)
{
if (x_72 == 0)
{
lean::dec(x_90);
if (x_72 == 0)
{
x_7 = x_72;
goto lbl_8;
}
else
{
x_9 = x_72;
goto lbl_10;
}
}
else
{
obj* x_94; uint8 x_95; 
x_94 = lean::mk_nat_obj(931u);
x_95 = lean::nat_dec_eq(x_90, x_94);
lean::dec(x_94);
lean::dec(x_90);
if (x_95 == 0)
{
if (x_72 == 0)
{
x_7 = x_72;
goto lbl_8;
}
else
{
x_9 = x_72;
goto lbl_10;
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
}
else
{
lean::dec(x_90);
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
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
uint8 x_1; uint8 x_3; obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::mk_nat_obj(8319u);
x_6 = lean::box_uint32(x_0);
x_7 = lean::nat_dec_le(x_5, x_6);
lean::dec(x_5);
if (x_7 == 0)
{
uint8 x_10; 
lean::dec(x_6);
x_10 = 0;
x_3 = x_10;
goto lbl_4;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(8329u);
x_12 = lean::nat_dec_le(x_6, x_11);
lean::dec(x_11);
lean::dec(x_6);
if (x_12 == 0)
{
uint8 x_15; 
x_15 = 0;
x_3 = x_15;
goto lbl_4;
}
else
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
}
lbl_2:
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::mk_nat_obj(7522u);
x_18 = lean::box_uint32(x_0);
x_19 = lean::nat_dec_le(x_17, x_18);
lean::dec(x_17);
if (x_19 == 0)
{
lean::dec(x_18);
return x_1;
}
else
{
obj* x_22; uint8 x_23; 
x_22 = lean::mk_nat_obj(7530u);
x_23 = lean::nat_dec_le(x_18, x_22);
lean::dec(x_22);
lean::dec(x_18);
if (x_23 == 0)
{
return x_1;
}
else
{
uint8 x_26; 
x_26 = 1;
return x_26;
}
}
}
lbl_4:
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::mk_nat_obj(8336u);
x_28 = lean::box_uint32(x_0);
x_29 = lean::nat_dec_le(x_27, x_28);
lean::dec(x_27);
if (x_29 == 0)
{
lean::dec(x_28);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(8348u);
x_33 = lean::nat_dec_le(x_28, x_32);
lean::dec(x_32);
lean::dec(x_28);
if (x_33 == 0)
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
uint8 x_36; 
x_36 = 1;
return x_36;
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
obj* x_2; obj* x_3; uint8 x_4; uint32 x_6; 
x_2 = lean::mk_nat_obj(95u);
x_3 = lean::mk_nat_obj(55296u);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(57343u);
x_9 = lean::nat_dec_lt(x_8, x_2);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_12; uint32 x_13; 
lean::dec(x_2);
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::unbox_uint32(x_12);
lean::dec(x_12);
x_6 = x_13;
goto lbl_7;
}
else
{
obj* x_15; uint8 x_16; 
x_15 = lean::mk_nat_obj(1114112u);
x_16 = lean::nat_dec_lt(x_2, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_19; uint32 x_20; 
lean::dec(x_2);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_6 = x_20;
goto lbl_7;
}
else
{
uint32 x_22; 
x_22 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = x_22;
goto lbl_7;
}
}
}
else
{
uint32 x_24; 
x_24 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = x_24;
goto lbl_7;
}
lbl_7:
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::box_uint32(x_0);
x_27 = lean::box_uint32(x_6);
x_28 = lean::nat_dec_eq(x_26, x_27);
lean::dec(x_27);
lean::dec(x_26);
if (x_28 == 0)
{
if (x_1 == 0)
{
uint8 x_31; 
x_31 = l_lean_is__letter__like(x_0);
return x_31;
}
else
{
return x_1;
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
else
{
if (x_1 == 0)
{
uint8 x_33; 
x_33 = l_lean_is__letter__like(x_0);
return x_33;
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
obj* x_4; obj* x_5; uint8 x_6; uint32 x_8; 
x_4 = lean::mk_nat_obj(95u);
x_5 = lean::mk_nat_obj(55296u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(57343u);
x_11 = lean::nat_dec_lt(x_10, x_4);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_14; uint32 x_15; 
lean::dec(x_4);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_8 = x_15;
goto lbl_9;
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(1114112u);
x_18 = lean::nat_dec_lt(x_4, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_21; uint32 x_22; 
lean::dec(x_4);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
x_8 = x_22;
goto lbl_9;
}
else
{
uint32 x_24; 
x_24 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_24;
goto lbl_9;
}
}
}
else
{
uint32 x_26; 
x_26 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_26;
goto lbl_9;
}
lbl_9:
{
obj* x_28; obj* x_29; uint8 x_30; 
x_28 = lean::box_uint32(x_0);
x_29 = lean::box_uint32(x_8);
x_30 = lean::nat_dec_eq(x_28, x_29);
lean::dec(x_29);
lean::dec(x_28);
if (x_30 == 0)
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
uint8 x_33; 
x_33 = l_lean_is__letter__like(x_0);
if (x_33 == 0)
{
uint8 x_34; 
x_34 = l_lean_is__sub__script__alnum(x_0);
return x_34;
}
else
{
return x_33;
}
}
else
{
if (x_3 == 0)
{
uint8 x_35; 
x_35 = l_lean_is__sub__script__alnum(x_0);
return x_35;
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
uint8 x_36; 
x_36 = 1;
return x_36;
}
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
uint8 x_37; 
x_37 = l_lean_is__letter__like(x_0);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_lean_is__sub__script__alnum(x_0);
return x_38;
}
else
{
return x_37;
}
}
else
{
if (x_3 == 0)
{
uint8 x_39; 
x_39 = l_lean_is__sub__script__alnum(x_0);
return x_39;
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
obj* x_40; obj* x_41; uint8 x_42; uint32 x_44; 
x_40 = lean::mk_nat_obj(39u);
x_41 = lean::mk_nat_obj(55296u);
x_42 = lean::nat_dec_lt(x_40, x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::mk_nat_obj(57343u);
x_47 = lean::nat_dec_lt(x_46, x_40);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_50; uint32 x_51; 
lean::dec(x_40);
x_50 = lean::mk_nat_obj(0u);
x_51 = lean::unbox_uint32(x_50);
lean::dec(x_50);
x_44 = x_51;
goto lbl_45;
}
else
{
obj* x_53; uint8 x_54; 
x_53 = lean::mk_nat_obj(1114112u);
x_54 = lean::nat_dec_lt(x_40, x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_57; uint32 x_58; 
lean::dec(x_40);
x_57 = lean::mk_nat_obj(0u);
x_58 = lean::unbox_uint32(x_57);
lean::dec(x_57);
x_44 = x_58;
goto lbl_45;
}
else
{
uint32 x_60; 
x_60 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_44 = x_60;
goto lbl_45;
}
}
}
else
{
uint32 x_62; 
x_62 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_44 = x_62;
goto lbl_45;
}
lbl_45:
{
obj* x_64; obj* x_65; uint8 x_66; 
x_64 = lean::box_uint32(x_0);
x_65 = lean::box_uint32(x_44);
x_66 = lean::nat_dec_eq(x_64, x_65);
lean::dec(x_65);
lean::dec(x_64);
if (x_66 == 0)
{
if (x_1 == 0)
{
uint8 x_69; 
x_69 = l_lean_is__letter__like(x_0);
if (x_69 == 0)
{
uint8 x_70; 
x_70 = l_lean_is__sub__script__alnum(x_0);
return x_70;
}
else
{
return x_69;
}
}
else
{
if (x_1 == 0)
{
uint8 x_71; 
x_71 = l_lean_is__sub__script__alnum(x_0);
return x_71;
}
else
{
return x_1;
}
}
}
else
{
uint8 x_72; 
x_72 = 1;
return x_72;
}
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
obj* _init_l_lean_id__begin__escape() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; 
x_0 = lean::mk_nat_obj(171u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(57343u);
x_5 = lean::nat_dec_lt(x_4, x_0);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(1114112u);
x_10 = lean::nat_dec_lt(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
if (x_10 == 0)
{
obj* x_13; 
x_13 = lean::mk_nat_obj(0u);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::mk_nat_obj(171u);
return x_14;
}
}
}
else
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::mk_nat_obj(171u);
return x_16;
}
}
}
obj* _init_l_lean_id__end__escape() {
_start:
{
obj* x_0; obj* x_1; uint8 x_2; 
x_0 = lean::mk_nat_obj(187u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(57343u);
x_5 = lean::nat_dec_lt(x_4, x_0);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(1114112u);
x_10 = lean::nat_dec_lt(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
if (x_10 == 0)
{
obj* x_13; 
x_13 = lean::mk_nat_obj(0u);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::mk_nat_obj(187u);
return x_14;
}
}
}
else
{
obj* x_16; 
lean::dec(x_0);
x_16 = lean::mk_nat_obj(187u);
return x_16;
}
}
}
uint8 l_lean_is__id__begin__escape(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_lean_id__begin__escape;
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_eq(x_2, x_1);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
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
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_lean_id__end__escape;
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_eq(x_2, x_1);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_31565857__take__while__aux___main___at_lean_parser_id__part__default___spec__4___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed), 2, 0);
return x_6;
}
}
obj* l_lean_parser_id__part__default___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_6);
x_11 = lean::apply_2(x_6, lean::box(0), x_8);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__default___rarg___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_6);
lean::inc(x_4);
x_15 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__default___spec__3___rarg___boxed), 2, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* l_lean_parser_id__part__default___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__1___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = l_lean_is__id__first(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_3);
lean::dec(x_2);
x_19 = l_char_quote__core(x_15);
x_20 = l_char_has__repr___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__default___spec__2___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* l_lean_parser_id__part__default(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__default___rarg), 3, 0);
return x_4;
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg), 6, 0);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_31565857__take__while__aux___main___at_lean_parser_id__part__escaped___spec__5___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed), 2, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_4);
lean::inc(x_2);
x_13 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_id__part__escaped___spec__4___rarg___boxed), 2, 1);
lean::closure_set(x_14, 0, x_1);
x_15 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__2___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = l_lean_is__id__end__escape(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_18 = lean::box_uint32(x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_19, 0, x_3);
lean::closure_set(x_19, 1, x_18);
x_20 = lean::apply_2(x_2, lean::box(0), x_19);
return x_20;
}
else
{
obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; 
lean::dec(x_3);
lean::dec(x_2);
x_23 = l_char_quote__core(x_15);
x_24 = l_char_has__repr___closed__1;
lean::inc(x_24);
x_26 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_28 = lean::string_append(x_26, x_24);
x_29 = lean::box(0);
x_30 = l_mjoin___rarg___closed__1;
lean::inc(x_29);
lean::inc(x_30);
x_33 = l_lean_parser_monad__parsec_error___at_lean_parser_id__part__escaped___spec__3___rarg(x_1, lean::box(0), x_28, x_30, x_29, x_29);
return x_33;
}
}
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_parser_id__part__escaped___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint32 x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; uint32 x_21; obj* x_22; obj* x_23; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 4);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_lean_id__begin__escape;
x_12 = lean::unbox_uint32(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_lean_parser_monad__parsec_ch___rarg(x_0, x_1, x_12);
lean::inc(x_1);
lean::inc(x_0);
x_18 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_id__part__escaped___spec__1___rarg(x_0, x_1);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_18);
x_20 = l_lean_id__end__escape;
x_21 = lean::unbox_uint32(x_20);
x_22 = l_lean_parser_monad__parsec_ch___rarg(x_0, x_1, x_21);
x_23 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_19, x_22);
return x_23;
}
}
obj* l_lean_parser_id__part__escaped(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part__escaped___rarg), 3, 0);
return x_4;
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
obj* l_lean_parser_id__part___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = l_lean_parser_id__part__escaped___rarg(x_0, x_1, x_2);
lean::inc(x_1);
lean::inc(x_0);
x_9 = l_lean_parser_id__part__default___rarg(x_0, x_1, x_2);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_monad__parsec_curr___rarg(x_0, x_1);
x_21 = l_lean_parser_id__part___rarg___closed__1;
lean::inc(x_21);
x_23 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_21, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_cond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_6);
x_25 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
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
obj* l_lean_parser_id__part(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_id__part___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg(obj* x_0, obj* x_1, uint32 x_2) {
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
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
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__2___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__3___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_14; obj* x_15; obj* x_17; uint32 x_19; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_36; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_14 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 4);
lean::inc(x_17);
x_19 = lean::unbox_uint32(x_5);
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg(x_0, x_1, x_19);
x_24 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_23, x_14);
x_25 = lean::cnstr_get(x_2, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::inc(x_3);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg___lambda__1), 6, 5);
lean::closure_set(x_30, 0, x_3);
lean::closure_set(x_30, 1, x_0);
lean::closure_set(x_30, 2, x_1);
lean::closure_set(x_30, 3, x_2);
lean::closure_set(x_30, 4, x_8);
x_31 = lean::apply_4(x_27, lean::box(0), lean::box(0), x_24, x_30);
x_32 = lean::cnstr_get(x_15, 1);
lean::inc(x_32);
lean::dec(x_15);
x_35 = lean::apply_2(x_32, lean::box(0), x_3);
x_36 = lean::apply_3(x_25, lean::box(0), x_31, x_35);
return x_36;
}
else
{
obj* x_41; obj* x_44; obj* x_47; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_41 = lean::cnstr_get(x_2, 0);
lean::inc(x_41);
lean::dec(x_2);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = lean::apply_2(x_44, lean::box(0), x_3);
return x_47;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::name_mk_string(x_0, x_5);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::box(0);
x_5 = lean::name_mk_string(x_4, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__5___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg(obj* x_0, obj* x_1, uint32 x_2) {
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
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
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__7___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__8___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_14; obj* x_15; obj* x_17; uint32 x_19; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_36; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_14 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 4);
lean::inc(x_17);
x_19 = lean::unbox_uint32(x_5);
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg(x_0, x_1, x_19);
x_24 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_23, x_14);
x_25 = lean::cnstr_get(x_2, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::inc(x_3);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg___lambda__1), 6, 5);
lean::closure_set(x_30, 0, x_3);
lean::closure_set(x_30, 1, x_0);
lean::closure_set(x_30, 2, x_1);
lean::closure_set(x_30, 3, x_2);
lean::closure_set(x_30, 4, x_8);
x_31 = lean::apply_4(x_27, lean::box(0), lean::box(0), x_24, x_30);
x_32 = lean::cnstr_get(x_15, 1);
lean::inc(x_32);
lean::dec(x_15);
x_35 = lean::apply_2(x_32, lean::box(0), x_3);
x_36 = lean::apply_3(x_25, lean::box(0), x_31, x_35);
return x_36;
}
else
{
obj* x_41; obj* x_44; obj* x_47; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_41 = lean::cnstr_get(x_2, 0);
lean::inc(x_41);
lean::dec(x_2);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = lean::apply_2(x_44, lean::box(0), x_3);
return x_47;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::name_mk_string(x_0, x_5);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::box(0);
x_5 = lean::name_mk_string(x_4, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__10___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg(obj* x_0, obj* x_1, uint32 x_2) {
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
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
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__12___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__13___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_15; obj* x_16; obj* x_18; obj* x_20; uint32 x_21; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 4);
lean::inc(x_18);
x_20 = lean::mk_nat_obj(46u);
x_21 = lean::unbox_uint32(x_20);
lean::dec(x_20);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg(x_0, x_1, x_21);
x_26 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_25, x_15);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
lean::inc(x_3);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg___lambda__1), 6, 5);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_0);
lean::closure_set(x_32, 2, x_1);
lean::closure_set(x_32, 3, x_2);
lean::closure_set(x_32, 4, x_9);
x_33 = lean::apply_4(x_29, lean::box(0), lean::box(0), x_26, x_32);
x_34 = lean::cnstr_get(x_16, 1);
lean::inc(x_34);
lean::dec(x_16);
x_37 = lean::apply_2(x_34, lean::box(0), x_3);
x_38 = lean::apply_3(x_27, lean::box(0), x_33, x_37);
return x_38;
}
else
{
obj* x_42; obj* x_45; obj* x_48; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_42 = lean::cnstr_get(x_2, 0);
lean::inc(x_42);
lean::dec(x_2);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = lean::apply_2(x_45, lean::box(0), x_3);
return x_48;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::name_mk_string(x_0, x_5);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::box(0);
x_5 = lean::name_mk_string(x_4, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__15___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg(obj* x_0, obj* x_1, uint32 x_2) {
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
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
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__17___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_identifier___spec__18___rarg(x_1, lean::box(0), x_29, x_31, x_30, x_30);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_15; obj* x_16; obj* x_18; obj* x_20; uint32 x_21; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 4);
lean::inc(x_18);
x_20 = lean::mk_nat_obj(46u);
x_21 = lean::unbox_uint32(x_20);
lean::dec(x_20);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg(x_0, x_1, x_21);
x_26 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_25, x_15);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
lean::inc(x_3);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg___lambda__1), 6, 5);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_0);
lean::closure_set(x_32, 2, x_1);
lean::closure_set(x_32, 3, x_2);
lean::closure_set(x_32, 4, x_9);
x_33 = lean::apply_4(x_29, lean::box(0), lean::box(0), x_26, x_32);
x_34 = lean::cnstr_get(x_16, 1);
lean::inc(x_34);
lean::dec(x_16);
x_37 = lean::apply_2(x_34, lean::box(0), x_3);
x_38 = lean::apply_3(x_27, lean::box(0), x_33, x_37);
return x_38;
}
else
{
obj* x_42; obj* x_45; obj* x_48; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_42 = lean::cnstr_get(x_2, 0);
lean::inc(x_42);
lean::dec(x_2);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = lean::apply_2(x_45, lean::box(0), x_3);
return x_48;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::name_mk_string(x_0, x_5);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::box(0);
x_5 = lean::name_mk_string(x_4, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at_lean_parser_identifier___spec__20___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_parser_id__part___rarg(x_0, x_1, x_2);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_identifier___rarg___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_2);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_15);
lean::inc(x_12);
x_18 = lean::apply_3(x_12, lean::box(0), x_15, x_11);
x_19 = l_lean_parser_identifier___rarg___closed__1;
lean::inc(x_19);
x_21 = lean::apply_3(x_12, lean::box(0), x_19, x_18);
return x_21;
}
}
obj* _init_l_lean_parser_identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::mk_nat_obj(46u);
x_5 = lean::mk_nat_obj(55296u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(57343u);
x_9 = lean::nat_dec_lt(x_8, x_4);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_12; 
lean::dec(x_4);
x_12 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_12;
}
else
{
obj* x_13; uint8 x_14; 
x_13 = lean::mk_nat_obj(1114112u);
x_14 = lean::nat_dec_lt(x_4, x_13);
lean::dec(x_13);
lean::dec(x_4);
if (x_14 == 0)
{
obj* x_17; 
x_17 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__9___rarg(x_0, x_1, x_2, x_3);
return x_17;
}
else
{
obj* x_18; 
x_18 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__14___rarg(x_0, x_1, x_2, x_3);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_4);
x_20 = l_lean_parser_monad__parsec_foldl___at_lean_parser_identifier___spec__19___rarg(x_0, x_1, x_2, x_3);
return x_20;
}
}
}
obj* l_lean_parser_identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_identifier___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__1___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__6___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__11___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_identifier___spec__16___rarg___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg), 6, 0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg), 6, 0);
return x_6;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint32 x_13; obj* x_14; uint8 x_16; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_16 = l_char_is__alphanum(x_13);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::mk_nat_obj(95u);
x_18 = lean::mk_nat_obj(55296u);
x_19 = lean::nat_dec_lt(x_17, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::mk_nat_obj(57343u);
x_22 = lean::nat_dec_lt(x_21, x_17);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_17);
x_25 = lean::box_uint32(x_13);
x_26 = lean::nat_dec_eq(x_25, x_3);
lean::dec(x_3);
lean::dec(x_25);
if (x_26 == 0)
{
if (x_16 == 0)
{
obj* x_30; 
lean::dec(x_10);
x_30 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::box(0);
x_14 = x_31;
goto lbl_15;
}
}
else
{
obj* x_32; 
x_32 = lean::box(0);
x_14 = x_32;
goto lbl_15;
}
}
else
{
obj* x_33; uint8 x_34; 
x_33 = lean::mk_nat_obj(1114112u);
x_34 = lean::nat_dec_lt(x_17, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_37; uint8 x_38; 
lean::dec(x_17);
x_37 = lean::box_uint32(x_13);
x_38 = lean::nat_dec_eq(x_37, x_3);
lean::dec(x_3);
lean::dec(x_37);
if (x_38 == 0)
{
if (x_16 == 0)
{
obj* x_42; 
lean::dec(x_10);
x_42 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_42;
}
else
{
obj* x_43; 
x_43 = lean::box(0);
x_14 = x_43;
goto lbl_15;
}
}
else
{
obj* x_44; 
x_44 = lean::box(0);
x_14 = x_44;
goto lbl_15;
}
}
else
{
obj* x_46; uint8 x_47; 
lean::dec(x_3);
x_46 = lean::box_uint32(x_13);
x_47 = lean::nat_dec_eq(x_46, x_17);
lean::dec(x_17);
lean::dec(x_46);
if (x_47 == 0)
{
if (x_16 == 0)
{
obj* x_51; 
lean::dec(x_10);
x_51 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_51;
}
else
{
obj* x_52; 
x_52 = lean::box(0);
x_14 = x_52;
goto lbl_15;
}
}
else
{
obj* x_53; 
x_53 = lean::box(0);
x_14 = x_53;
goto lbl_15;
}
}
}
}
else
{
obj* x_55; uint8 x_56; 
lean::dec(x_3);
x_55 = lean::box_uint32(x_13);
x_56 = lean::nat_dec_eq(x_55, x_17);
lean::dec(x_17);
lean::dec(x_55);
if (x_56 == 0)
{
if (x_16 == 0)
{
obj* x_60; 
lean::dec(x_10);
x_60 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::box(0);
x_14 = x_61;
goto lbl_15;
}
}
else
{
obj* x_62; 
x_62 = lean::box(0);
x_14 = x_62;
goto lbl_15;
}
}
}
else
{
lean::dec(x_3);
if (x_16 == 0)
{
obj* x_65; 
lean::dec(x_10);
x_65 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::box(0);
x_14 = x_66;
goto lbl_15;
}
}
lbl_15:
{
obj* x_68; obj* x_69; 
lean::dec(x_14);
x_68 = lean::string_push(x_1, x_13);
x_69 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_68;
x_2 = x_69;
goto _start;
}
}
}
else
{
obj* x_73; 
lean::dec(x_3);
lean::dec(x_0);
x_73 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_73;
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = l___private_31565857__take__while__aux___main___at_lean_parser_c__identifier___spec__4___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___boxed), 2, 0);
return x_6;
}
}
obj* l_lean_parser_c__identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_6);
x_11 = lean::apply_2(x_6, lean::box(0), x_8);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_c__identifier___rarg___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_6);
lean::inc(x_4);
x_15 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
lean::inc(x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___boxed), 2, 1);
lean::closure_set(x_17, 0, x_1);
x_18 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_15, x_17);
x_19 = lean::cnstr_get(x_1, 1);
lean::inc(x_19);
lean::dec(x_1);
x_22 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_22);
lean::inc(x_19);
x_25 = lean::apply_3(x_19, lean::box(0), x_22, x_18);
x_26 = l_lean_parser_c__identifier___rarg___closed__1;
lean::inc(x_26);
x_28 = lean::apply_3(x_19, lean::box(0), x_26, x_25);
return x_28;
}
}
obj* _init_l_lean_parser_c__identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_c__identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__1___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
uint32 x_15; obj* x_16; uint8 x_18; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = l_char_is__alpha(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::mk_nat_obj(95u);
x_20 = lean::mk_nat_obj(55296u);
x_21 = lean::nat_dec_lt(x_19, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_19);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
lean::dec(x_19);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::box_uint32(x_15);
x_29 = lean::nat_dec_eq(x_28, x_27);
lean::dec(x_27);
if (x_29 == 0)
{
if (x_18 == 0)
{
obj* x_34; 
lean::dec(x_28);
lean::dec(x_3);
lean::dec(x_2);
x_34 = lean::box(0);
x_16 = x_34;
goto lbl_17;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_36, 0, x_3);
lean::closure_set(x_36, 1, x_28);
x_37 = lean::apply_2(x_2, lean::box(0), x_36);
return x_37;
}
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_1);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_39, 0, x_3);
lean::closure_set(x_39, 1, x_28);
x_40 = lean::apply_2(x_2, lean::box(0), x_39);
return x_40;
}
}
else
{
obj* x_41; uint8 x_42; 
x_41 = lean::mk_nat_obj(1114112u);
x_42 = lean::nat_dec_lt(x_19, x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; uint8 x_47; 
lean::dec(x_19);
x_45 = lean::mk_nat_obj(0u);
x_46 = lean::box_uint32(x_15);
x_47 = lean::nat_dec_eq(x_46, x_45);
lean::dec(x_45);
if (x_47 == 0)
{
if (x_18 == 0)
{
obj* x_52; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_46);
x_52 = lean::box(0);
x_16 = x_52;
goto lbl_17;
}
else
{
obj* x_54; obj* x_55; 
lean::dec(x_1);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_54, 0, x_3);
lean::closure_set(x_54, 1, x_46);
x_55 = lean::apply_2(x_2, lean::box(0), x_54);
return x_55;
}
}
else
{
obj* x_57; obj* x_58; 
lean::dec(x_1);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_57, 0, x_3);
lean::closure_set(x_57, 1, x_46);
x_58 = lean::apply_2(x_2, lean::box(0), x_57);
return x_58;
}
}
else
{
obj* x_59; uint8 x_60; 
x_59 = lean::box_uint32(x_15);
x_60 = lean::nat_dec_eq(x_59, x_19);
lean::dec(x_19);
if (x_60 == 0)
{
if (x_18 == 0)
{
obj* x_65; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_59);
x_65 = lean::box(0);
x_16 = x_65;
goto lbl_17;
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_1);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_67, 0, x_3);
lean::closure_set(x_67, 1, x_59);
x_68 = lean::apply_2(x_2, lean::box(0), x_67);
return x_68;
}
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_1);
x_70 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_70, 0, x_3);
lean::closure_set(x_70, 1, x_59);
x_71 = lean::apply_2(x_2, lean::box(0), x_70);
return x_71;
}
}
}
}
else
{
obj* x_72; uint8 x_73; 
x_72 = lean::box_uint32(x_15);
x_73 = lean::nat_dec_eq(x_72, x_19);
lean::dec(x_19);
if (x_73 == 0)
{
if (x_18 == 0)
{
obj* x_78; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_72);
x_78 = lean::box(0);
x_16 = x_78;
goto lbl_17;
}
else
{
obj* x_80; obj* x_81; 
lean::dec(x_1);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_80, 0, x_3);
lean::closure_set(x_80, 1, x_72);
x_81 = lean::apply_2(x_2, lean::box(0), x_80);
return x_81;
}
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_1);
x_83 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_83, 0, x_3);
lean::closure_set(x_83, 1, x_72);
x_84 = lean::apply_2(x_2, lean::box(0), x_83);
return x_84;
}
}
}
else
{
if (x_18 == 0)
{
obj* x_87; 
lean::dec(x_3);
lean::dec(x_2);
x_87 = lean::box(0);
x_16 = x_87;
goto lbl_17;
}
else
{
obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
x_89 = lean::box_uint32(x_15);
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_90, 0, x_3);
lean::closure_set(x_90, 1, x_89);
x_91 = lean::apply_2(x_2, lean::box(0), x_90);
return x_91;
}
}
lbl_17:
{
obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_103; 
lean::dec(x_16);
x_93 = l_char_quote__core(x_15);
x_94 = l_char_has__repr___closed__1;
lean::inc(x_94);
x_96 = lean::string_append(x_94, x_93);
lean::dec(x_93);
x_98 = lean::string_append(x_96, x_94);
x_99 = lean::box(0);
x_100 = l_mjoin___rarg___closed__1;
lean::inc(x_99);
lean::inc(x_100);
x_103 = l_lean_parser_monad__parsec_error___at_lean_parser_c__identifier___spec__2___rarg(x_1, lean::box(0), x_98, x_100, x_99, x_99);
return x_103;
}
}
}
}
obj* l_lean_parser_c__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_c__identifier___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_c__identifier___spec__3___rarg(x_0, x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; 
lean::inc(x_2);
x_5 = l_string_is__empty(x_2);
if (x_5 == 0)
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_str__core___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_23; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_string_join___closed__1;
lean::inc(x_21);
x_23 = lean::apply_2(x_18, lean::box(0), x_21);
return x_23;
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_cpp__identifier___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_23; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_parser_c__identifier___rarg(x_0, x_1, x_2);
lean::inc(x_3);
lean::inc(x_8);
lean::inc(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg___lambda__2), 6, 5);
lean::closure_set(x_12, 0, x_2);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
lean::closure_set(x_12, 3, x_8);
lean::closure_set(x_12, 4, x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = l_lean_parser_monad__parsec_try___rarg___closed__1;
lean::inc(x_17);
lean::inc(x_14);
x_20 = lean::apply_3(x_14, lean::box(0), x_17, x_13);
x_21 = l_lean_parser_cpp__identifier___rarg___closed__1;
lean::inc(x_21);
x_23 = lean::apply_3(x_14, lean::box(0), x_21, x_20);
return x_23;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C++ identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_labels___rarg___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = l_list_foldl___main___at_string_join___spec__1(x_7, x_6);
x_10 = lean::apply_2(x_3, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_cpp__identifier___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
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
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_lean_parser_monad__parsec_str__core___at_lean_parser_cpp__identifier___spec__1___rarg(x_1, x_2, x_15, x_16);
x_22 = l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3;
lean::inc(x_22);
x_24 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_22, x_21);
x_25 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_24, x_3);
x_26 = l_lean_parser_monad__parsec_many___rarg(x_1, x_2, lean::box(0), x_0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg___lambda__1), 3, 2);
lean::closure_set(x_27, 0, x_6);
lean::closure_set(x_27, 1, x_5);
x_28 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_26, x_27);
return x_28;
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
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_append), 2, 0);
return x_0;
}
}
obj* l_lean_parser_cpp__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_cpp__identifier___rarg), 3, 0);
return x_4;
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
 l_lean_id__end__escape = _init_l_lean_id__end__escape();
 l_lean_parser_id__part___rarg___closed__1 = _init_l_lean_parser_id__part___rarg___closed__1();
 l_lean_parser_identifier___rarg___closed__1 = _init_l_lean_parser_identifier___rarg___closed__1();
 l_lean_parser_c__identifier___rarg___closed__1 = _init_l_lean_parser_c__identifier___rarg___closed__1();
 l_lean_parser_cpp__identifier___rarg___closed__1 = _init_l_lean_parser_cpp__identifier___rarg___closed__1();
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__1();
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__2();
 l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3 = _init_l_lean_parser_cpp__identifier___rarg___lambda__2___closed__3();
}
