// Lean compiler output
// Module: init.lean.name_mangling
// Imports: init.lean.name init.lean.parser.stringliteral
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
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
obj* l_Lean_Name_mangle(obj*, obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___main(obj*, obj*, obj*);
extern obj* l___private_init_data_string_basic_9__toNatCore___main___closed__1;
obj* l___private_init_lean_parser_parsec_3__mkStringResult___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__8(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1;
obj* l___private_init_lean_name__mangling_6__parseMangledName(obj*, obj*);
extern uint32 l_Nat_digitChar___closed__2;
obj* l_Lean_String_demangle(obj*);
extern uint32 l___private_init_data_string_basic_3__utf8GetAux___main___closed__1;
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(obj*);
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(uint32, obj*);
obj* l_Lean_Name_mangle___boxed(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
extern obj* l_mjoin___rarg___closed__1;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
uint8 l_Char_isAlpha(uint32);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4;
uint32 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
obj* l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6(obj*);
obj* l_id___rarg___boxed(obj*);
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2;
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__7(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
extern uint32 l_Nat_digitChar___closed__7;
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main___boxed(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_String_Iterator_remaining___main(obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___main___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern usize l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
obj* l_matchFailed___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__11(obj*);
obj* l_Lean_String_demangle___closed__1;
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1;
obj* l_String_Iterator_next___main(obj*);
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_4__Name_mangleAux(obj*, obj*);
obj* l___private_init_lean_name__mangling_3__parseMangledString(obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__4(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_mod(obj*, obj*);
}
uint32 l_Char_ofNat(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_alpha___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__5(obj*);
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_digit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__4(obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__3(obj*);
obj* l_Lean_Parser_MonadParsec_take___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__10(obj*, obj*);
obj* l_Lean_String_mangle(obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2;
extern obj* l_matchFailed___rarg___closed__1;
obj* l_Dlist_singleton___rarg(obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1;
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___boxed(obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___boxed(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_num___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__2(obj*);
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux(obj*, obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1;
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
obj* l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
obj* l___private_init_lean_parser_parsec_1__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__6(obj*, obj*);
uint8 l_String_Iterator_hasNext___main(obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3(obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__9(obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main(obj*, obj*, obj*);
uint32 l_Nat_digitChar(obj*);
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3___boxed;
obj* l_String_quote(obj*);
extern uint32 l_Lean_Parser_parseHexDigit___rarg___lambda__4___closed__1;
obj* l_Lean_Name_demangle(obj*, obj*);
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__5(obj*, obj*, obj*);
extern obj* l_String_Iterator_extract___main___closed__1;
extern obj* l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_u");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_x");
return x_0;
}
}
uint32 _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3() {
_start:
{
obj* x_0; uint32 x_1; 
x_0 = lean::mk_nat_obj(95u);
x_1 = l_Char_ofNat(x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("__");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux___main(obj* x_0, obj* x_1, obj* x_2) {
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
x_8 = l_String_Iterator_curr___main(x_1);
x_11 = l_Char_isAlpha(x_8);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = l_Char_isDigit(x_8);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
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
x_16 = l_String_Iterator_next___main(x_1);
x_17 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4;
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
x_20 = l_String_Iterator_next___main(x_1);
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
x_23 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
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
x_26 = l_String_Iterator_next___main(x_1);
x_27 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4;
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
x_30 = l_String_Iterator_next___main(x_1);
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
x_37 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
x_38 = lean::string_append(x_2, x_37);
x_39 = lean::mk_nat_obj(4096u);
x_40 = lean::nat_div(x_34, x_39);
x_41 = l_Nat_digitChar(x_40);
lean::dec(x_40);
x_43 = lean::string_push(x_38, x_41);
x_44 = lean::nat_mod(x_34, x_39);
lean::dec(x_34);
x_46 = lean::mk_nat_obj(256u);
x_47 = lean::nat_div(x_44, x_46);
x_48 = l_Nat_digitChar(x_47);
lean::dec(x_47);
x_50 = lean::string_push(x_43, x_48);
x_51 = lean::nat_mod(x_44, x_46);
lean::dec(x_44);
x_53 = lean::mk_nat_obj(16u);
x_54 = lean::nat_div(x_51, x_53);
x_55 = l_Nat_digitChar(x_54);
lean::dec(x_54);
x_57 = lean::string_push(x_50, x_55);
x_58 = lean::nat_mod(x_51, x_53);
lean::dec(x_51);
x_60 = l_Nat_digitChar(x_58);
lean::dec(x_58);
x_62 = lean::string_push(x_57, x_60);
x_63 = l_String_Iterator_next___main(x_1);
x_0 = x_6;
x_1 = x_63;
x_2 = x_62;
goto _start;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; uint32 x_69; obj* x_71; obj* x_72; uint32 x_74; obj* x_76; obj* x_77; 
x_65 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
x_66 = lean::string_append(x_2, x_65);
x_67 = lean::mk_nat_obj(16u);
x_68 = lean::nat_div(x_34, x_67);
x_69 = l_Nat_digitChar(x_68);
lean::dec(x_68);
x_71 = lean::string_push(x_66, x_69);
x_72 = lean::nat_mod(x_34, x_67);
lean::dec(x_34);
x_74 = l_Nat_digitChar(x_72);
lean::dec(x_72);
x_76 = lean::string_push(x_71, x_74);
x_77 = l_String_Iterator_next___main(x_1);
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
obj* _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l___private_init_lean_name__mangling_1__String_mangleAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_String_mangle(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; usize x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::string_length(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_4 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_3);
x_5 = x_4;
x_6 = l_String_Iterator_extract___main___closed__1;
x_7 = l___private_init_lean_name__mangling_1__String_mangleAux___main(x_1, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_isEmpty(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; usize x_6; obj* x_8; obj* x_9; obj* x_11; 
x_4 = lean::string_length(x_0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = x_8;
lean::inc(x_2);
x_11 = l___private_init_lean_parser_parsec_1__strAux___main(x_4, x_9, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_13 = lean::box(0);
x_14 = l_String_Iterator_extract___main___closed__1;
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_1);
lean::cnstr_set(x_15, 3, x_13);
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
x_21 = lean::cnstr_get(x_11, 0);
lean::inc(x_21);
lean::dec(x_11);
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
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_0);
x_28 = l_String_Iterator_extract___main___closed__1;
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_Option_getOrElse___main___rarg(x_2, x_4);
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
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__4(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_Iterator_hasNext___main(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_Iterator_curr___main(x_0);
x_10 = l_Char_isDigit(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_String_Iterator_next___main(x_0);
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
obj* _init_l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_Lean_Parser_MonadParsec_digit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__4(x_0);
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
x_16 = l___private_init_data_string_basic_9__toNatCore___main___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
x_23 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_24 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_21, x_23);
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
x_42 = l_String_Iterator_hasNext___main(x_0);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
x_46 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_44, x_45, x_43, x_43, x_0);
x_40 = x_46;
goto lbl_41;
}
else
{
uint32 x_47; uint32 x_48; uint8 x_49; 
x_47 = l_String_Iterator_curr___main(x_0);
x_48 = l_Nat_digitChar___closed__7;
x_49 = x_48 <= x_47;
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = l_Char_quoteCore(x_47);
x_51 = l_Char_HasRepr___closed__1;
x_52 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_54 = lean::string_append(x_52, x_51);
x_55 = lean::box(0);
x_56 = l_mjoin___rarg___closed__1;
x_57 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_54, x_56, x_55, x_55, x_0);
x_40 = x_57;
goto lbl_41;
}
else
{
uint32 x_58; uint8 x_59; 
x_58 = l_Nat_digitChar___closed__2;
x_59 = x_47 <= x_58;
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_60 = l_Char_quoteCore(x_47);
x_61 = l_Char_HasRepr___closed__1;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_64 = lean::string_append(x_62, x_61);
x_65 = lean::box(0);
x_66 = l_mjoin___rarg___closed__1;
x_67 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_64, x_66, x_65, x_65, x_0);
x_40 = x_67;
goto lbl_41;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::inc(x_0);
x_69 = l_String_Iterator_next___main(x_0);
x_70 = lean::box(0);
x_71 = lean::box_uint32(x_47);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_69);
lean::cnstr_set(x_72, 2, x_70);
x_40 = x_72;
goto lbl_41;
}
}
}
lbl_41:
{
obj* x_73; obj* x_74; 
x_73 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_40);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint32 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_75 = lean::cnstr_get(x_74, 0);
x_77 = lean::cnstr_get(x_74, 1);
x_79 = lean::cnstr_get(x_74, 2);
if (lean::is_exclusive(x_74)) {
 x_81 = x_74;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_74);
 x_81 = lean::box(0);
}
x_82 = lean::unbox_uint32(x_75);
x_83 = lean::uint32_to_nat(x_82);
x_84 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_85 = lean::nat_sub(x_83, x_84);
lean::dec(x_83);
x_87 = lean::mk_nat_obj(10u);
x_88 = lean::nat_add(x_87, x_85);
lean::dec(x_85);
if (lean::is_scalar(x_81)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_81;
}
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_77);
lean::cnstr_set(x_90, 2, x_73);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_0);
x_93 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_91);
x_94 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_95 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_93, x_94);
return x_95;
}
else
{
obj* x_96; uint8 x_98; 
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
x_35 = x_91;
x_36 = x_96;
x_37 = x_98;
goto lbl_38;
}
}
else
{
obj* x_99; uint8 x_101; obj* x_102; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_74, 0);
x_101 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_102 = x_74;
} else {
 lean::inc(x_99);
 lean::dec(x_74);
 x_102 = lean::box(0);
}
lean::inc(x_99);
if (lean::is_scalar(x_102)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_102;
}
lean::cnstr_set(x_104, 0, x_99);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_101);
x_105 = x_104;
x_35 = x_105;
x_36 = x_99;
x_37 = x_101;
goto lbl_38;
}
}
}
else
{
obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_2);
x_108 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_109 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_1, x_108);
return x_109;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_111; uint8 x_113; 
lean::dec(x_35);
x_113 = l_String_Iterator_hasNext___main(x_0);
if (x_113 == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::box(0);
x_115 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_116 = l_mjoin___rarg___closed__1;
x_117 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_115, x_116, x_114, x_114, x_0);
lean::dec(x_0);
x_111 = x_117;
goto lbl_112;
}
else
{
uint32 x_119; uint32 x_120; uint8 x_121; 
x_119 = l_String_Iterator_curr___main(x_0);
x_120 = l___private_init_data_string_basic_3__utf8GetAux___main___closed__1;
x_121 = x_120 <= x_119;
if (x_121 == 0)
{
obj* x_122; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_122 = l_Char_quoteCore(x_119);
x_123 = l_Char_HasRepr___closed__1;
x_124 = lean::string_append(x_123, x_122);
lean::dec(x_122);
x_126 = lean::string_append(x_124, x_123);
x_127 = lean::box(0);
x_128 = l_mjoin___rarg___closed__1;
x_129 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_126, x_128, x_127, x_127, x_0);
lean::dec(x_0);
x_111 = x_129;
goto lbl_112;
}
else
{
uint32 x_131; uint8 x_132; 
x_131 = l_Lean_Parser_parseHexDigit___rarg___lambda__4___closed__1;
x_132 = x_119 <= x_131;
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_133 = l_Char_quoteCore(x_119);
x_134 = l_Char_HasRepr___closed__1;
x_135 = lean::string_append(x_134, x_133);
lean::dec(x_133);
x_137 = lean::string_append(x_135, x_134);
x_138 = lean::box(0);
x_139 = l_mjoin___rarg___closed__1;
x_140 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_137, x_139, x_138, x_138, x_0);
lean::dec(x_0);
x_111 = x_140;
goto lbl_112;
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_142 = l_String_Iterator_next___main(x_0);
x_143 = lean::box(0);
x_144 = lean::box_uint32(x_119);
x_145 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_142);
lean::cnstr_set(x_145, 2, x_143);
x_111 = x_145;
goto lbl_112;
}
}
}
lbl_112:
{
obj* x_146; obj* x_147; 
x_146 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_147 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_146, x_111);
if (lean::obj_tag(x_147) == 0)
{
obj* x_148; obj* x_150; obj* x_152; obj* x_154; uint32 x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_148 = lean::cnstr_get(x_147, 0);
x_150 = lean::cnstr_get(x_147, 1);
x_152 = lean::cnstr_get(x_147, 2);
if (lean::is_exclusive(x_147)) {
 x_154 = x_147;
} else {
 lean::inc(x_148);
 lean::inc(x_150);
 lean::inc(x_152);
 lean::dec(x_147);
 x_154 = lean::box(0);
}
x_155 = lean::unbox_uint32(x_148);
x_156 = lean::uint32_to_nat(x_155);
x_157 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_158 = lean::nat_sub(x_156, x_157);
lean::dec(x_156);
x_160 = lean::mk_nat_obj(10u);
x_161 = lean::nat_add(x_160, x_158);
lean::dec(x_158);
if (lean::is_scalar(x_154)) {
 x_163 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_163 = x_154;
}
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_150);
lean::cnstr_set(x_163, 2, x_146);
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_152, x_163);
x_165 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_36, x_164);
x_166 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_165);
x_167 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_168 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_166, x_167);
return x_168;
}
else
{
obj* x_169; uint8 x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_169 = lean::cnstr_get(x_147, 0);
x_171 = lean::cnstr_get_scalar<uint8>(x_147, sizeof(void*)*1);
if (lean::is_exclusive(x_147)) {
 x_172 = x_147;
} else {
 lean::inc(x_169);
 lean::dec(x_147);
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
x_175 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_36, x_174);
x_176 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_175);
x_177 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_178 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_176, x_177);
return x_178;
}
}
}
else
{
obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_0);
lean::dec(x_36);
x_181 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_35);
x_182 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1;
x_183 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_181, x_182);
return x_183;
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_alpha___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__5(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_Iterator_hasNext___main(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_Iterator_curr___main(x_0);
x_10 = l_Char_isAlpha(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_String_Iterator_next___main(x_0);
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
obj* _init_l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_String_Iterator_remaining___main(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint32 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_5 = l_String_Iterator_curr___main(x_0);
x_6 = l_Char_quoteCore(x_5);
x_7 = l_Char_HasRepr___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_10 = lean::string_append(x_8, x_7);
x_11 = lean::box(0);
x_12 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_13 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_10, x_12, x_11, x_11, x_0);
lean::dec(x_0);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::box(0);
x_18 = l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1;
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_0);
lean::cnstr_set(x_19, 2, x_18);
return x_19;
}
}
}
obj* _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_u");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_x");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("__");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::inc(x_2);
x_10 = l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6(x_2);
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
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_16);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_18);
x_7 = x_19;
goto lbl_8;
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
x_7 = x_25;
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
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_38; 
lean::dec(x_7);
lean::inc(x_2);
x_38 = l_Lean_Parser_MonadParsec_alpha___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__5(x_2);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_43; uint32 x_46; obj* x_48; obj* x_49; obj* x_50; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_46 = lean::unbox_uint32(x_39);
lean::inc(x_1);
x_48 = lean::string_push(x_1, x_46);
x_49 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_6, x_48, x_41);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_54 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_50);
return x_54;
}
else
{
obj* x_55; uint8 x_57; 
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
x_32 = x_50;
x_33 = x_55;
x_34 = x_57;
goto lbl_35;
}
}
else
{
obj* x_58; uint8 x_60; obj* x_61; obj* x_63; obj* x_64; 
x_58 = lean::cnstr_get(x_38, 0);
x_60 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 x_61 = x_38;
} else {
 lean::inc(x_58);
 lean::dec(x_38);
 x_61 = lean::box(0);
}
lean::inc(x_58);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_60);
x_64 = x_63;
x_32 = x_64;
x_33 = x_58;
x_34 = x_60;
goto lbl_35;
}
}
else
{
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_29);
return x_7;
}
lbl_35:
{
obj* x_69; obj* x_70; uint8 x_71; 
if (x_34 == 0)
{
obj* x_75; 
lean::dec(x_32);
lean::inc(x_2);
x_75 = l_Lean_Parser_MonadParsec_digit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__4(x_2);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; uint32 x_83; obj* x_85; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
x_83 = lean::unbox_uint32(x_76);
lean::inc(x_1);
x_85 = lean::string_push(x_1, x_83);
x_86 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_6, x_85, x_78);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_91; obj* x_92; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_91 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_87);
x_92 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_91);
return x_92;
}
else
{
obj* x_93; uint8 x_95; 
x_93 = lean::cnstr_get(x_87, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
x_69 = x_87;
x_70 = x_93;
x_71 = x_95;
goto lbl_72;
}
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_101; obj* x_102; 
x_96 = lean::cnstr_get(x_75, 0);
x_98 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_exclusive(x_75)) {
 x_99 = x_75;
} else {
 lean::inc(x_96);
 lean::dec(x_75);
 x_99 = lean::box(0);
}
lean::inc(x_96);
if (lean::is_scalar(x_99)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_99;
}
lean::cnstr_set(x_101, 0, x_96);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_98);
x_102 = x_101;
x_69 = x_102;
x_70 = x_96;
x_71 = x_98;
goto lbl_72;
}
}
else
{
obj* x_107; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_33);
x_107 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_32);
return x_107;
}
lbl_72:
{
obj* x_108; obj* x_109; uint8 x_110; 
if (x_71 == 0)
{
obj* x_113; obj* x_114; obj* x_116; 
lean::dec(x_69);
x_113 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4;
x_114 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3;
lean::inc(x_2);
x_116 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(x_113, x_114, x_2);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_119; uint32 x_122; obj* x_124; obj* x_125; obj* x_126; 
x_117 = lean::cnstr_get(x_116, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_116, 2);
lean::inc(x_119);
lean::dec(x_116);
x_122 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
lean::inc(x_1);
x_124 = lean::string_push(x_1, x_122);
x_125 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_6, x_124, x_117);
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_119, x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_130 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_126);
x_131 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_130);
x_132 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_131);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_126, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_126, sizeof(void*)*1);
x_108 = x_126;
x_109 = x_133;
x_110 = x_135;
goto lbl_111;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_116, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_116, sizeof(void*)*1);
if (lean::is_exclusive(x_116)) {
 x_139 = x_116;
} else {
 lean::inc(x_136);
 lean::dec(x_116);
 x_139 = lean::box(0);
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
x_108 = x_142;
x_109 = x_136;
x_110 = x_138;
goto lbl_111;
}
}
else
{
obj* x_147; obj* x_148; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_70);
x_147 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_69);
x_148 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_147);
return x_148;
}
lbl_111:
{
obj* x_149; obj* x_150; uint8 x_151; 
if (x_110 == 0)
{
obj* x_154; obj* x_155; obj* x_157; 
lean::dec(x_108);
x_154 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2;
x_155 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2;
lean::inc(x_2);
x_157 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(x_154, x_155, x_2);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_160; obj* x_163; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_157, 2);
lean::inc(x_160);
lean::dec(x_157);
x_163 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_158);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_166; obj* x_168; obj* x_171; 
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_163, 1);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_163, 2);
lean::inc(x_168);
lean::dec(x_163);
x_171 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_166);
if (lean::obj_tag(x_171) == 0)
{
obj* x_172; obj* x_174; obj* x_176; obj* x_179; obj* x_180; obj* x_182; uint32 x_185; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_172 = lean::cnstr_get(x_171, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_171, 2);
lean::inc(x_176);
lean::dec(x_171);
x_179 = lean::mk_nat_obj(16u);
x_180 = lean::nat_mul(x_164, x_179);
lean::dec(x_164);
x_182 = lean::nat_add(x_180, x_172);
lean::dec(x_172);
lean::dec(x_180);
x_185 = l_Char_ofNat(x_182);
lean::dec(x_182);
lean::inc(x_1);
x_188 = lean::string_push(x_1, x_185);
x_189 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_6, x_188, x_174);
x_190 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_176, x_189);
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_168, x_190);
x_192 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_160, x_191);
if (lean::obj_tag(x_192) == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_196 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_192);
x_197 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_196);
x_198 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_197);
x_199 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_198);
return x_199;
}
else
{
obj* x_200; uint8 x_202; 
x_200 = lean::cnstr_get(x_192, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*1);
x_149 = x_192;
x_150 = x_200;
x_151 = x_202;
goto lbl_152;
}
}
else
{
obj* x_204; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_164);
x_204 = lean::cnstr_get(x_171, 0);
x_206 = lean::cnstr_get_scalar<uint8>(x_171, sizeof(void*)*1);
if (lean::is_exclusive(x_171)) {
 x_207 = x_171;
} else {
 lean::inc(x_204);
 lean::dec(x_171);
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
x_210 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_168, x_209);
x_211 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_160, x_210);
if (lean::obj_tag(x_211) == 0)
{
obj* x_215; obj* x_216; obj* x_217; obj* x_218; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_215 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_211);
x_216 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_215);
x_217 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_216);
x_218 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_217);
return x_218;
}
else
{
obj* x_219; uint8 x_221; 
x_219 = lean::cnstr_get(x_211, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get_scalar<uint8>(x_211, sizeof(void*)*1);
x_149 = x_211;
x_150 = x_219;
x_151 = x_221;
goto lbl_152;
}
}
}
else
{
obj* x_222; uint8 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_222 = lean::cnstr_get(x_163, 0);
x_224 = lean::cnstr_get_scalar<uint8>(x_163, sizeof(void*)*1);
if (lean::is_exclusive(x_163)) {
 x_225 = x_163;
} else {
 lean::inc(x_222);
 lean::dec(x_163);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set_scalar(x_226, sizeof(void*)*1, x_224);
x_227 = x_226;
x_228 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_160, x_227);
if (lean::obj_tag(x_228) == 0)
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_232 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_228);
x_233 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_232);
x_234 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_233);
x_235 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_234);
return x_235;
}
else
{
obj* x_236; uint8 x_238; 
x_236 = lean::cnstr_get(x_228, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_228, sizeof(void*)*1);
x_149 = x_228;
x_150 = x_236;
x_151 = x_238;
goto lbl_152;
}
}
}
else
{
obj* x_239; uint8 x_241; obj* x_242; obj* x_244; obj* x_245; 
x_239 = lean::cnstr_get(x_157, 0);
x_241 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
if (lean::is_exclusive(x_157)) {
 x_242 = x_157;
} else {
 lean::inc(x_239);
 lean::dec(x_157);
 x_242 = lean::box(0);
}
lean::inc(x_239);
if (lean::is_scalar(x_242)) {
 x_244 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_244 = x_242;
}
lean::cnstr_set(x_244, 0, x_239);
lean::cnstr_set_scalar(x_244, sizeof(void*)*1, x_241);
x_245 = x_244;
x_149 = x_245;
x_150 = x_239;
x_151 = x_241;
goto lbl_152;
}
}
else
{
obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_109);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_250 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_108);
x_251 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_250);
x_252 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_251);
return x_252;
}
lbl_152:
{
if (x_151 == 0)
{
obj* x_254; obj* x_255; obj* x_256; 
lean::dec(x_149);
x_254 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1;
x_255 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1;
x_256 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(x_254, x_255, x_2);
if (lean::obj_tag(x_256) == 0)
{
obj* x_257; obj* x_259; obj* x_262; 
x_257 = lean::cnstr_get(x_256, 1);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_256, 2);
lean::inc(x_259);
lean::dec(x_256);
x_262 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_257);
if (lean::obj_tag(x_262) == 0)
{
obj* x_263; obj* x_265; obj* x_267; obj* x_270; 
x_263 = lean::cnstr_get(x_262, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get(x_262, 1);
lean::inc(x_265);
x_267 = lean::cnstr_get(x_262, 2);
lean::inc(x_267);
lean::dec(x_262);
x_270 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_265);
if (lean::obj_tag(x_270) == 0)
{
obj* x_271; obj* x_273; obj* x_275; obj* x_278; 
x_271 = lean::cnstr_get(x_270, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_270, 1);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_270, 2);
lean::inc(x_275);
lean::dec(x_270);
x_278 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_273);
if (lean::obj_tag(x_278) == 0)
{
obj* x_279; obj* x_281; obj* x_283; obj* x_286; 
x_279 = lean::cnstr_get(x_278, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_278, 1);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_278, 2);
lean::inc(x_283);
lean::dec(x_278);
x_286 = l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2(x_281);
if (lean::obj_tag(x_286) == 0)
{
obj* x_287; obj* x_289; obj* x_291; obj* x_294; obj* x_295; obj* x_297; obj* x_298; obj* x_300; obj* x_303; obj* x_304; obj* x_306; obj* x_309; uint32 x_312; obj* x_314; obj* x_315; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; 
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_286, 2);
lean::inc(x_291);
lean::dec(x_286);
x_294 = lean::mk_nat_obj(4096u);
x_295 = lean::nat_mul(x_263, x_294);
lean::dec(x_263);
x_297 = lean::mk_nat_obj(256u);
x_298 = lean::nat_mul(x_271, x_297);
lean::dec(x_271);
x_300 = lean::nat_add(x_295, x_298);
lean::dec(x_298);
lean::dec(x_295);
x_303 = lean::mk_nat_obj(16u);
x_304 = lean::nat_mul(x_279, x_303);
lean::dec(x_279);
x_306 = lean::nat_add(x_300, x_304);
lean::dec(x_304);
lean::dec(x_300);
x_309 = lean::nat_add(x_306, x_287);
lean::dec(x_287);
lean::dec(x_306);
x_312 = l_Char_ofNat(x_309);
lean::dec(x_309);
x_314 = lean::string_push(x_1, x_312);
x_315 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_6, x_314, x_289);
lean::dec(x_6);
x_317 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_291, x_315);
x_318 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_283, x_317);
x_319 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_275, x_318);
x_320 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_267, x_319);
x_321 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_320);
x_322 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_321);
x_323 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_322);
x_324 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_323);
x_325 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_324);
x_326 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_325);
return x_326;
}
else
{
obj* x_332; uint8 x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_263);
lean::dec(x_279);
lean::dec(x_271);
x_332 = lean::cnstr_get(x_286, 0);
x_334 = lean::cnstr_get_scalar<uint8>(x_286, sizeof(void*)*1);
if (lean::is_exclusive(x_286)) {
 x_335 = x_286;
} else {
 lean::inc(x_332);
 lean::dec(x_286);
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
x_338 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_283, x_337);
x_339 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_275, x_338);
x_340 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_267, x_339);
x_341 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_340);
x_342 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_341);
x_343 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_342);
x_344 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_343);
x_345 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_344);
x_346 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_345);
return x_346;
}
}
else
{
obj* x_351; uint8 x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_263);
lean::dec(x_271);
x_351 = lean::cnstr_get(x_278, 0);
x_353 = lean::cnstr_get_scalar<uint8>(x_278, sizeof(void*)*1);
if (lean::is_exclusive(x_278)) {
 x_354 = x_278;
} else {
 lean::inc(x_351);
 lean::dec(x_278);
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
x_357 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_275, x_356);
x_358 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_267, x_357);
x_359 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_358);
x_360 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_359);
x_361 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_360);
x_362 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_361);
x_363 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_362);
x_364 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_363);
return x_364;
}
}
else
{
obj* x_368; uint8 x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_263);
x_368 = lean::cnstr_get(x_270, 0);
x_370 = lean::cnstr_get_scalar<uint8>(x_270, sizeof(void*)*1);
if (lean::is_exclusive(x_270)) {
 x_371 = x_270;
} else {
 lean::inc(x_368);
 lean::dec(x_270);
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
x_374 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_267, x_373);
x_375 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_374);
x_376 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_375);
x_377 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_376);
x_378 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_377);
x_379 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_378);
x_380 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_379);
return x_380;
}
}
else
{
obj* x_383; uint8 x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_6);
lean::dec(x_1);
x_383 = lean::cnstr_get(x_262, 0);
x_385 = lean::cnstr_get_scalar<uint8>(x_262, sizeof(void*)*1);
if (lean::is_exclusive(x_262)) {
 x_386 = x_262;
} else {
 lean::inc(x_383);
 lean::dec(x_262);
 x_386 = lean::box(0);
}
if (lean::is_scalar(x_386)) {
 x_387 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_387 = x_386;
}
lean::cnstr_set(x_387, 0, x_383);
lean::cnstr_set_scalar(x_387, sizeof(void*)*1, x_385);
x_388 = x_387;
x_389 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_388);
x_390 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_389);
x_391 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_390);
x_392 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_391);
x_393 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_392);
x_394 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_393);
return x_394;
}
}
else
{
obj* x_397; uint8 x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; 
lean::dec(x_6);
lean::dec(x_1);
x_397 = lean::cnstr_get(x_256, 0);
x_399 = lean::cnstr_get_scalar<uint8>(x_256, sizeof(void*)*1);
if (lean::is_exclusive(x_256)) {
 x_400 = x_256;
} else {
 lean::inc(x_397);
 lean::dec(x_256);
 x_400 = lean::box(0);
}
if (lean::is_scalar(x_400)) {
 x_401 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_401 = x_400;
}
lean::cnstr_set(x_401, 0, x_397);
lean::cnstr_set_scalar(x_401, sizeof(void*)*1, x_399);
x_402 = x_401;
x_403 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_150, x_402);
x_404 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_403);
x_405 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_404);
x_406 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_405);
x_407 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_406);
return x_407;
}
}
else
{
obj* x_412; obj* x_413; obj* x_414; obj* x_415; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_150);
x_412 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_109, x_149);
x_413 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_70, x_412);
x_414 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_413);
x_415 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_414);
return x_415;
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
obj* x_416; obj* x_417; 
x_416 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_417 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_417, 0, x_1);
lean::cnstr_set(x_417, 1, x_2);
lean::cnstr_set(x_417, 2, x_416);
return x_417;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_2__parseMangledStringAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_2__parseMangledStringAux(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_3__parseMangledString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = l_String_Iterator_remaining___main(x_0);
x_2 = l_String_Iterator_extract___main___closed__1;
x_3 = l___private_init_lean_name__mangling_2__parseMangledStringAux___main(x_1, x_2, x_0);
lean::dec(x_1);
x_5 = l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1;
x_6 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_3);
return x_6;
}
}
obj* _init_l_Lean_String_demangle___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_name__mangling_3__parseMangledString), 1, 0);
return x_0;
}
}
obj* l_Lean_String_demangle(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_String_demangle___closed__1;
x_2 = l_String_Iterator_extract___main___closed__1;
x_3 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_1, x_0, x_2);
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
obj* _init_l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_s");
return x_0;
}
}
obj* _init_l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_");
return x_0;
}
}
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main(obj* x_0, obj* x_1) {
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
x_8 = l___private_init_lean_name__mangling_4__Name_mangleAux___main(x_0, x_3);
x_9 = l_Lean_String_mangle(x_5);
x_10 = l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1;
x_11 = lean::string_append(x_8, x_10);
x_12 = lean::string_length(x_9);
x_13 = l_Nat_repr(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
x_16 = l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2;
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
x_25 = l___private_init_lean_name__mangling_4__Name_mangleAux___main(x_0, x_20);
x_26 = l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2;
x_27 = lean::string_append(x_25, x_26);
x_28 = l_Nat_repr(x_22);
x_29 = lean::string_append(x_27, x_28);
lean::dec(x_28);
x_31 = lean::string_append(x_29, x_26);
return x_31;
}
}
}
}
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__Name_mangleAux___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_name__mangling_4__Name_mangleAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__Name_mangleAux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_name__mangling_4__Name_mangleAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__Name_mangleAux(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Name_mangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_name__mangling_4__Name_mangleAux___main(x_1, x_0);
return x_2;
}
}
obj* l_Lean_Name_mangle___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Name_mangle(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(uint32 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_Iterator_hasNext___main(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
lean::dec(x_1);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_1);
x_11 = x_10 == x_0;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_12 = l_Char_quoteCore(x_10);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_16, x_18, x_17, x_17, x_1);
lean::dec(x_1);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = l_String_Iterator_next___main(x_1);
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
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_Iterator_next___main(x_2);
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
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__5(x_2, x_0, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_Iterator_next___main(x_2);
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
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__7(x_2, x_0, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_Iterator_next___main(x_2);
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
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__9(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__3(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_Iterator_hasNext___main(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint32 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_String_Iterator_extract___main___closed__1;
x_17 = lean::unbox_uint32(x_9);
x_18 = lean::string_push(x_16, x_17);
x_19 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__4(x_18, x_11);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_19);
return x_20;
}
else
{
obj* x_21; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_8, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_24 = x_8;
} else {
 lean::inc(x_21);
 lean::dec(x_8);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_23);
x_26 = x_25;
return x_26;
}
}
else
{
uint32 x_27; uint8 x_28; 
x_27 = l_String_Iterator_curr___main(x_0);
x_28 = l_Char_isDigit(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; 
x_29 = l_Char_quoteCore(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_33 = lean::string_append(x_31, x_30);
x_34 = lean::box(0);
x_35 = l_mjoin___rarg___closed__1;
x_36 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__3___rarg(x_33, x_35, x_34, x_34, x_0);
lean::dec(x_0);
x_38 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_47; uint32 x_48; obj* x_49; obj* x_50; obj* x_51; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_39, 2);
lean::inc(x_44);
lean::dec(x_39);
x_47 = l_String_Iterator_extract___main___closed__1;
x_48 = lean::unbox_uint32(x_40);
x_49 = lean::string_push(x_47, x_48);
x_50 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__6(x_49, x_42);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_50);
return x_51;
}
else
{
obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_39, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_exclusive(x_39)) {
 x_55 = x_39;
} else {
 lean::inc(x_52);
 lean::dec(x_39);
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
return x_57;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_58 = l_String_Iterator_next___main(x_0);
x_59 = lean::box(0);
x_60 = l_String_Iterator_extract___main___closed__1;
x_61 = lean::string_push(x_60, x_27);
x_62 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__8(x_61, x_58);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_62);
return x_63;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_num___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__3(x_0);
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
x_9 = l_String_toNat(x_2);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_10);
x_12 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_11);
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
obj* l_Lean_Parser_MonadParsec_take___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = l_String_Iterator_extract___main___closed__1;
x_5 = l___private_init_lean_parser_parsec_2__takeAux___main___rarg(x_0, x_4, x_1);
return x_5;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_0);
x_7 = l_String_Iterator_extract___main___closed__1;
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
}
}
obj* l_matchFailed___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__11(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_1 = l_matchFailed___rarg___closed__1;
x_2 = l_mjoin___rarg___closed__1;
x_3 = l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
}
}
obj* _init_l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("_s");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::inc(x_2);
x_10 = l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6(x_2);
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
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_1);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_16);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_18);
x_7 = x_19;
goto lbl_8;
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
x_7 = x_25;
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
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_7);
x_37 = l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1;
x_38 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1;
lean::inc(x_2);
x_40 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(x_37, x_38, x_2);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_43; obj* x_46; 
x_41 = lean::cnstr_get(x_40, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_Lean_Parser_MonadParsec_num___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__2(x_41);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; uint32 x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_54 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
x_55 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(x_54, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_61; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 2);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_Lean_Parser_MonadParsec_take___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__10(x_47, x_56);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
x_66 = lean::cnstr_get(x_61, 2);
if (lean::is_exclusive(x_61)) {
 x_68 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_61);
 x_68 = lean::box(0);
}
x_69 = l_Lean_String_demangle(x_62);
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_68)) {
 x_71 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_71 = x_68;
}
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_64);
lean::cnstr_set(x_71, 2, x_70);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; 
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_75; obj* x_77; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_72, 2);
lean::inc(x_77);
lean::dec(x_72);
x_80 = l_matchFailed___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__11(x_75);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_88; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_88 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_84);
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
x_92 = lean::cnstr_get(x_72, 1);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_72, 2);
lean::inc(x_94);
lean::dec(x_72);
x_97 = lean::cnstr_get(x_73, 0);
lean::inc(x_97);
lean::dec(x_73);
lean::inc(x_1);
x_101 = lean_name_mk_string(x_1, x_97);
x_102 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main(x_6, x_101, x_92);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_94, x_102);
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_103);
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_104);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_110; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_110 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_106);
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
x_114 = lean::cnstr_get(x_72, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
if (lean::is_exclusive(x_72)) {
 x_117 = x_72;
} else {
 lean::inc(x_114);
 lean::dec(x_72);
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
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_120);
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_126; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_126 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_122);
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
x_130 = lean::cnstr_get(x_61, 0);
x_132 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_133 = x_61;
} else {
 lean::inc(x_130);
 lean::dec(x_61);
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
x_136 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_135);
x_137 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_136);
x_138 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_142; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_142 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_138);
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
x_147 = lean::cnstr_get(x_55, 0);
x_149 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_150 = x_55;
} else {
 lean::inc(x_147);
 lean::dec(x_55);
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
x_153 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_152);
x_154 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_158; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_158 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_154);
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
x_168 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_172; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_172 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_168);
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
return x_7;
}
lbl_35:
{
if (x_34 == 0)
{
uint32 x_188; obj* x_189; 
lean::dec(x_32);
x_188 = l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3;
x_189 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(x_188, x_2);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; obj* x_192; obj* x_195; 
x_190 = lean::cnstr_get(x_189, 1);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 2);
lean::inc(x_192);
lean::dec(x_189);
x_195 = l_Lean_Parser_MonadParsec_num___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__2(x_190);
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
x_203 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(x_188, x_198);
if (lean::obj_tag(x_203) == 0)
{
obj* x_204; obj* x_206; obj* x_209; obj* x_210; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
x_204 = lean::cnstr_get(x_203, 1);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 2);
lean::inc(x_206);
lean::dec(x_203);
x_209 = lean_name_mk_numeral(x_1, x_196);
x_210 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main(x_6, x_209, x_204);
lean::dec(x_6);
x_212 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_206, x_210);
x_213 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_212);
x_214 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_213);
x_215 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_214);
x_216 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_215);
return x_216;
}
else
{
obj* x_220; uint8 x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_196);
x_220 = lean::cnstr_get(x_203, 0);
x_222 = lean::cnstr_get_scalar<uint8>(x_203, sizeof(void*)*1);
if (lean::is_exclusive(x_203)) {
 x_223 = x_203;
} else {
 lean::inc(x_220);
 lean::dec(x_203);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_220);
lean::cnstr_set_scalar(x_224, sizeof(void*)*1, x_222);
x_225 = x_224;
x_226 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_225);
x_227 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_226);
x_228 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_227);
x_229 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_228);
return x_229;
}
}
else
{
obj* x_232; uint8 x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_6);
lean::dec(x_1);
x_232 = lean::cnstr_get(x_195, 0);
x_234 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_exclusive(x_195)) {
 x_235 = x_195;
} else {
 lean::inc(x_232);
 lean::dec(x_195);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_232);
lean::cnstr_set_scalar(x_236, sizeof(void*)*1, x_234);
x_237 = x_236;
x_238 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_237);
x_239 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_238);
x_240 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_239);
return x_240;
}
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_6);
lean::dec(x_1);
x_243 = lean::cnstr_get(x_189, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*1);
if (lean::is_exclusive(x_189)) {
 x_246 = x_189;
} else {
 lean::inc(x_243);
 lean::dec(x_189);
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
x_249 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_248);
x_250 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_249);
return x_250;
}
}
else
{
obj* x_255; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_33);
x_255 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_32);
return x_255;
}
}
}
}
}
else
{
obj* x_256; obj* x_257; 
x_256 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_257 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_257, 0, x_1);
lean::cnstr_set(x_257, 1, x_2);
lean::cnstr_set(x_257, 2, x_256);
return x_257;
}
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_name__mangling_5__parseMangledNameAux___main___spec__1(x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_5__parseMangledNameAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_name__mangling_5__parseMangledNameAux(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_name__mangling_6__parseMangledName(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = l_String_quote(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__1(x_0, x_4, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_String_Iterator_remaining___main(x_6);
x_12 = lean::box(0);
x_13 = l___private_init_lean_name__mangling_5__parseMangledNameAux___main(x_11, x_12, x_6);
lean::dec(x_11);
x_15 = l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_13);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_5, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_21 = x_5;
} else {
 lean::inc(x_18);
 lean::dec(x_5);
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
}
obj* l_Lean_Name_demangle(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_name__mangling_6__parseMangledName), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_2, x_0, x_3);
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
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_parser_stringliteral(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_name__mangling(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_stringliteral(w);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__1);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__2);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3();
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4 = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__4);
 l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3___boxed = _init_l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3___boxed();
lean::mark_persistent(l___private_init_lean_name__mangling_1__String_mangleAux___main___closed__3___boxed);
 l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1 = _init_l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHexDigit___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__2___closed__1);
 l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1 = _init_l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_eoi___at___private_init_lean_name__mangling_2__parseMangledStringAux___main___spec__6___closed__1);
 l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1 = _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__1);
 l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2 = _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__2);
 l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3 = _init_l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_name__mangling_2__parseMangledStringAux___main___closed__3);
 l_Lean_String_demangle___closed__1 = _init_l_Lean_String_demangle___closed__1();
lean::mark_persistent(l_Lean_String_demangle___closed__1);
 l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1 = _init_l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__1);
 l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2 = _init_l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_name__mangling_4__Name_mangleAux___main___closed__2);
 l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1 = _init_l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_name__mangling_5__parseMangledNameAux___main___closed__1);
return w;
}
