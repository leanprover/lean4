// Lean compiler output
// Module: init.lean.ir.lirc
// Imports: init.lean.ir.parser init.lean.ir.type_check init.lean.ir.ssa_check init.lean.ir.extract_cpp init.lean.ir.format init.lean.ir.elim_phi
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
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_ir_lirc___boxed(obj*, obj*, obj*);
uint8 l_char_is__whitespace(uint32);
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
obj* l_lean_ir_elim__phi(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_ir_check(obj*, uint8, obj*);
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(obj*);
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(obj*, uint8, obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_ir_parse__decl(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(uint32, obj*);
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4(obj*, obj*);
obj* l_lean_ir_parse__input___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(obj*);
obj* l_lean_ir_symbol(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_option_orelse___main___rarg(obj*, obj*);
uint8 l_char_is__alpha(uint32);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_ir_parse__input___lambda__1(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_function_comp___rarg(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__fnid2string;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_ir_lirc(obj*, obj*, uint8);
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_extract__cpp(obj*, obj*);
obj* l_lean_parser_parsec_message_to__string___rarg(obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_ir_check__blockids(obj*);
extern obj* l_list_repr___main___rarg___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_ir_parse__input__aux(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_update__env(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___boxed(obj*);
obj* l_lean_ir_parse__input__aux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_ir_lirc___spec__2(obj*);
extern obj* l_lean_ir_var_declare___closed__1;
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(obj*);
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_lean_ir_parse__input(obj*);
obj* l_lean_ir_decl_valid__ssa(obj*);
obj* l_lean_ir_parse__input__aux___main(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_iterator_remaining(obj*);
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_ir_decl_name(obj*);
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(obj*, obj*);
obj* l_lean_ir_parse__input__aux___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_check___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
uint8 l_char_is__alphanum(uint32);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5___boxed(obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_ir_type__check(obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___boxed(obj*);
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
uint8 l_rbnode_is__red___main___rarg(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(obj*, uint8, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(obj*, obj*, obj*);
obj* l_lean_ir_update__external__names(obj*, obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_8; obj* x_9; uint32 x_11; uint8 x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = lean::string_iterator_curr(x_2);
x_12 = l_char_is__alphanum(x_11);
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 95;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
if (x_12 == 0)
{
obj* x_16; 
lean::dec(x_9);
x_16 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::string_push(x_1, x_11);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_9;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::string_push(x_1, x_11);
x_21 = lean::string_iterator_next(x_2);
x_0 = x_9;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
else
{
if (x_12 == 0)
{
obj* x_24; 
lean::dec(x_9);
x_24 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::string_push(x_1, x_11);
x_26 = lean::string_iterator_next(x_2);
x_0 = x_9;
x_1 = x_25;
x_2 = x_26;
goto _start;
}
}
}
}
else
{
obj* x_29; 
lean::dec(x_0);
x_29 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_29;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_0);
x_4 = lean::string_iterator_remaining(x_1);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(x_4, x_3, x_1);
return x_5;
}
}
obj* _init_l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_5, x_6, x_4, x_4, x_0);
lean::dec(x_0);
x_1 = x_7;
goto lbl_2;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_char_is__alpha(x_9);
if (x_10 == 0)
{
uint32 x_11; uint8 x_12; 
x_11 = 95;
x_12 = x_9 == x_11;
if (x_12 == 0)
{
if (x_10 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = l_char_quote__core(x_9);
x_14 = l_char_has__repr___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_17 = lean::string_append(x_15, x_14);
x_18 = lean::box(0);
x_19 = l_mjoin___rarg___closed__1;
x_20 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_17, x_19, x_18, x_18, x_0);
lean::dec(x_0);
x_1 = x_20;
goto lbl_2;
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
x_1 = x_25;
goto lbl_2;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::string_iterator_next(x_0);
x_27 = lean::box(0);
x_28 = lean::box_uint32(x_9);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_27);
x_1 = x_29;
goto lbl_2;
}
}
else
{
if (x_10 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = l_char_quote__core(x_9);
x_31 = l_char_has__repr___closed__1;
x_32 = lean::string_append(x_31, x_30);
lean::dec(x_30);
x_34 = lean::string_append(x_32, x_31);
x_35 = lean::box(0);
x_36 = l_mjoin___rarg___closed__1;
x_37 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_34, x_36, x_35, x_35, x_0);
lean::dec(x_0);
x_1 = x_37;
goto lbl_2;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = lean::string_iterator_next(x_0);
x_40 = lean::box(0);
x_41 = lean::box_uint32(x_9);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_39);
lean::cnstr_set(x_42, 2, x_40);
x_1 = x_42;
goto lbl_2;
}
}
}
lbl_2:
{
obj* x_43; obj* x_44; 
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_1);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_47; obj* x_49; uint32 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 2);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::unbox_uint32(x_45);
x_53 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_52, x_47);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_53);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
x_56 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_55, x_56);
return x_57;
}
else
{
obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_68; obj* x_69; uint8 x_70; obj* x_71; obj* x_72; 
x_58 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_60 = x_44;
} else {
 lean::inc(x_58);
 lean::dec(x_44);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_58, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_58, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_58, 3);
lean::inc(x_65);
lean::dec(x_58);
x_68 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_61);
lean::cnstr_set(x_69, 1, x_63);
lean::cnstr_set(x_69, 2, x_68);
lean::cnstr_set(x_69, 3, x_65);
x_70 = 0;
if (lean::is_scalar(x_60)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_60;
}
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_70);
x_72 = x_71;
return x_72;
}
}
}
}
obj* l_lean_ir_parse__input__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_12; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
x_8 = lean::box(0);
lean::inc(x_3);
x_12 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_12, 1);
x_15 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
lean::inc(x_1);
x_19 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_2);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_17;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_23);
x_9 = x_24;
goto lbl_10;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_12, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_28 = x_12;
} else {
 lean::inc(x_25);
 lean::dec(x_12);
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
x_9 = x_30;
goto lbl_10;
}
lbl_10:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
x_35 = lean::cnstr_get(x_9, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_37 == 0)
{
obj* x_45; obj* x_47; 
lean::dec(x_9);
x_45 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
x_47 = l_lean_ir_symbol(x_45, x_3);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_50; obj* x_53; 
x_48 = lean::cnstr_get(x_47, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 2);
lean::inc(x_50);
lean::dec(x_47);
x_53 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_48);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_61; 
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_53, 2);
lean::inc(x_58);
lean::dec(x_53);
x_61 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_56);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
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
lean::cnstr_set(x_68, 0, x_54);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_78; obj* x_79; 
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_70, 2);
lean::inc(x_75);
lean::dec(x_70);
x_78 = l_list_repr___main___rarg___closed__3;
x_79 = l_lean_ir_symbol(x_78, x_73);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_80 = lean::cnstr_get(x_79, 1);
x_82 = lean::cnstr_get(x_79, 2);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_71);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_67);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_86);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_88);
x_42 = x_89;
goto lbl_43;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_71);
x_91 = lean::cnstr_get(x_79, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_exclusive(x_79)) {
 x_94 = x_79;
} else {
 lean::inc(x_91);
 lean::dec(x_79);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_96);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_97);
x_42 = x_98;
goto lbl_43;
}
}
else
{
obj* x_99; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_70, 0);
x_101 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_exclusive(x_70)) {
 x_102 = x_70;
} else {
 lean::inc(x_99);
 lean::dec(x_70);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_99);
lean::cnstr_set_scalar(x_103, sizeof(void*)*1, x_101);
x_104 = x_103;
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_104);
x_42 = x_105;
goto lbl_43;
}
}
else
{
obj* x_107; uint8 x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_54);
x_107 = lean::cnstr_get(x_61, 0);
x_109 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_110 = x_61;
} else {
 lean::inc(x_107);
 lean::dec(x_61);
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
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_116; obj* x_118; obj* x_121; obj* x_122; 
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_113, 2);
lean::inc(x_118);
lean::dec(x_113);
x_121 = l_list_repr___main___rarg___closed__3;
x_122 = l_lean_ir_symbol(x_121, x_116);
if (lean::obj_tag(x_122) == 0)
{
obj* x_123; obj* x_125; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_123 = lean::cnstr_get(x_122, 1);
x_125 = lean::cnstr_get(x_122, 2);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 x_127 = x_122;
} else {
 lean::inc(x_123);
 lean::inc(x_125);
 lean::dec(x_122);
 x_127 = lean::box(0);
}
x_128 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_128, 0, x_114);
x_129 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_127)) {
 x_130 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_130 = x_127;
}
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_123);
lean::cnstr_set(x_130, 2, x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_130);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_132);
x_42 = x_133;
goto lbl_43;
}
else
{
obj* x_135; uint8 x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_114);
x_135 = lean::cnstr_get(x_122, 0);
x_137 = lean::cnstr_get_scalar<uint8>(x_122, sizeof(void*)*1);
if (lean::is_exclusive(x_122)) {
 x_138 = x_122;
} else {
 lean::inc(x_135);
 lean::dec(x_122);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_135);
lean::cnstr_set_scalar(x_139, sizeof(void*)*1, x_137);
x_140 = x_139;
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_140);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_141);
x_42 = x_142;
goto lbl_43;
}
}
else
{
obj* x_143; uint8 x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_143 = lean::cnstr_get(x_113, 0);
x_145 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
if (lean::is_exclusive(x_113)) {
 x_146 = x_113;
} else {
 lean::inc(x_143);
 lean::dec(x_113);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_143);
lean::cnstr_set_scalar(x_147, sizeof(void*)*1, x_145);
x_148 = x_147;
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_148);
x_42 = x_149;
goto lbl_43;
}
}
}
else
{
obj* x_150; uint8 x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_150 = lean::cnstr_get(x_53, 0);
x_152 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_exclusive(x_53)) {
 x_153 = x_53;
} else {
 lean::inc(x_150);
 lean::dec(x_53);
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
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_155);
x_42 = x_156;
goto lbl_43;
}
}
else
{
obj* x_157; uint8 x_159; obj* x_160; obj* x_161; obj* x_162; 
x_157 = lean::cnstr_get(x_47, 0);
x_159 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_160 = x_47;
} else {
 lean::inc(x_157);
 lean::dec(x_47);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*1, x_159);
x_162 = x_161;
x_42 = x_162;
goto lbl_43;
}
}
else
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_35);
return x_9;
}
lbl_41:
{
obj* x_168; 
x_168 = l_lean_ir_parse__decl(x_39);
if (lean::obj_tag(x_168) == 0)
{
if (lean::obj_tag(x_38) == 0)
{
obj* x_169; obj* x_171; obj* x_173; obj* x_176; obj* x_177; obj* x_179; obj* x_180; obj* x_181; 
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_168, 2);
lean::inc(x_173);
lean::dec(x_168);
x_176 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_176, 0, x_169);
lean::cnstr_set(x_176, 1, x_1);
x_177 = l_lean_ir_parse__input__aux___main(x_7, x_176, x_2, x_171);
lean::dec(x_7);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_173, x_177);
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_179);
x_181 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_180);
return x_181;
}
else
{
obj* x_182; obj* x_184; obj* x_186; obj* x_189; obj* x_193; obj* x_194; obj* x_196; obj* x_197; obj* x_199; obj* x_200; obj* x_201; 
x_182 = lean::cnstr_get(x_168, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_168, 1);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_168, 2);
lean::inc(x_186);
lean::dec(x_168);
x_189 = lean::cnstr_get(x_38, 0);
lean::inc(x_189);
lean::dec(x_38);
lean::inc(x_182);
x_193 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_193, 0, x_182);
lean::cnstr_set(x_193, 1, x_1);
x_194 = l_lean_ir_decl_name(x_182);
lean::dec(x_182);
x_196 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_194, x_189);
x_197 = l_lean_ir_parse__input__aux___main(x_7, x_193, x_196, x_184);
lean::dec(x_7);
x_199 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_186, x_197);
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_199);
x_201 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_200);
return x_201;
}
}
else
{
obj* x_206; uint8 x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_206 = lean::cnstr_get(x_168, 0);
x_208 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_exclusive(x_168)) {
 x_209 = x_168;
} else {
 lean::inc(x_206);
 lean::dec(x_168);
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
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_211);
x_213 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_212);
return x_213;
}
}
lbl_43:
{
obj* x_214; 
if (lean::obj_tag(x_42) == 0)
{
obj* x_217; 
lean::dec(x_3);
x_217 = lean::box(0);
x_214 = x_217;
goto lbl_215;
}
else
{
obj* x_218; uint8 x_220; 
x_218 = lean::cnstr_get(x_42, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (x_220 == 0)
{
obj* x_222; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_42);
x_222 = lean::cnstr_get(x_218, 2);
lean::inc(x_222);
lean::dec(x_218);
x_225 = l_mjoin___rarg___closed__1;
x_226 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_226, 0, x_222);
lean::closure_set(x_226, 1, x_225);
x_227 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_227, 0, x_226);
x_38 = x_8;
x_39 = x_3;
x_40 = x_227;
goto lbl_41;
}
else
{
obj* x_230; 
lean::dec(x_218);
lean::dec(x_3);
x_230 = lean::box(0);
x_214 = x_230;
goto lbl_215;
}
}
lbl_215:
{
lean::dec(x_214);
if (lean::obj_tag(x_42) == 0)
{
obj* x_232; obj* x_234; obj* x_236; 
x_232 = lean::cnstr_get(x_42, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_42, 1);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_42, 2);
lean::inc(x_236);
lean::dec(x_42);
x_38 = x_232;
x_39 = x_234;
x_40 = x_236;
goto lbl_41;
}
else
{
obj* x_242; uint8 x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_242 = lean::cnstr_get(x_42, 0);
x_244 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_245 = x_42;
} else {
 lean::inc(x_242);
 lean::dec(x_42);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_242);
lean::cnstr_set_scalar(x_246, sizeof(void*)*1, x_244);
x_247 = x_246;
x_248 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_247);
return x_248;
}
}
}
}
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
x_249 = l_list_reverse___rarg(x_1);
x_250 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_2);
x_251 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_252 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_252, 0, x_250);
lean::cnstr_set(x_252, 1, x_3);
lean::cnstr_set(x_252, 2, x_251);
return x_252;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_2, x_1);
return x_3;
}
}
obj* l_lean_ir_parse__input__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_ir_parse__input__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_parse__input__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_parse__input__aux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
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
obj* l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = 0;
x_3 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(x_1, x_2, x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while_x_27___at_lean_ir_parse__input___spec__2(x_0);
return x_1;
}
}
obj* l_lean_ir_parse__input___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_ir_mk__fnid2string;
x_10 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_9, x_4);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_10);
return x_11;
}
else
{
obj* x_13; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_16 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
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
obj* l_lean_ir_parse__input(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__input___lambda__1___boxed), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = l_string_join___closed__1;
x_5 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_3, x_0, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_8 = x_5;
} else {
 lean::inc(x_6);
 lean::dec(x_5);
 x_8 = lean::box(0);
}
x_9 = l_lean_parser_parsec_message_to__string___rarg(x_6);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l_lean_ir_parse__input___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__input___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_ir_check(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_12; 
lean::dec(x_4);
x_12 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_15 = x_12;
} else {
 lean::inc(x_13);
 lean::dec(x_12);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
else
{
obj* x_18; 
lean::dec(x_12);
x_18 = l_lean_ir_var_declare___closed__1;
return x_18;
}
}
}
else
{
obj* x_20; 
lean::inc(x_2);
x_20 = l_lean_ir_decl_valid__ssa(x_2);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_25 = x_20;
} else {
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_20);
lean::inc(x_2);
x_29 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
return x_35;
}
else
{
obj* x_37; 
lean::dec(x_29);
x_37 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_40 = x_37;
} else {
 lean::inc(x_38);
 lean::dec(x_37);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
return x_41;
}
else
{
obj* x_43; 
lean::dec(x_37);
x_43 = l_lean_ir_var_declare___closed__1;
return x_43;
}
}
}
}
}
}
obj* l_lean_ir_check___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_check(x_0, x_3, x_2);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_ir_decl_name(x_2);
x_8 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_7, x_2);
x_0 = x_8;
x_1 = x_4;
goto _start;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt___main(x_1, x_5);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
obj* x_15; uint8 x_17; 
lean::dec(x_3);
x_15 = l_lean_name_quick__lt___main(x_5, x_1);
lean::dec(x_5);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_19; 
lean::dec(x_9);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_7);
return x_19;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_update__env(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_lean_ir_update__env___spec__4(x_3, x_0);
x_5 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_4, x_2);
x_6 = lean::apply_1(x_1, x_2);
x_7 = l_option_orelse___main___rarg(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_ir_update__env___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_ir_update__env___spec__5(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt___main(x_1, x_5);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
obj* x_15; uint8 x_17; 
lean::dec(x_3);
x_15 = l_lean_name_quick__lt___main(x_5, x_1);
lean::dec(x_5);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_19; 
lean::dec(x_9);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_7);
return x_19;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_update__external__names(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_2);
x_4 = lean::apply_1(x_1, x_2);
x_5 = l_option_orelse___main___rarg(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_lean_ir_var_declare___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
lean::inc(x_2);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_15, 0, x_2);
lean::closure_set(x_15, 1, x_12);
x_16 = l_lean_ir_check(x_15, x_1, x_7);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_22 = x_16;
} else {
 lean::inc(x_20);
 lean::dec(x_16);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
lean::dec(x_16);
x_3 = x_9;
goto _start;
}
}
}
}
obj* l_list_map___main___at_lean_ir_lirc___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_lean_ir_elim__phi(x_2);
x_8 = l_list_map___main___at_lean_ir_lirc___spec__2(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_lean_ir_lirc(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_parse__input(x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_14; obj* x_20; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
lean::inc(x_12);
lean::inc(x_12);
lean::inc(x_1);
x_20 = l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(x_1, x_2, x_12, x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_26 = x_20;
} else {
 lean::inc(x_24);
 lean::dec(x_20);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; 
lean::dec(x_20);
x_29 = lean::cnstr_get(x_1, 3);
lean::inc(x_29);
lean::inc(x_12);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_32, 0, x_12);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::cnstr_get(x_1, 4);
lean::inc(x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__external__names), 3, 2);
lean::closure_set(x_35, 0, x_14);
lean::closure_set(x_35, 1, x_33);
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 5);
lean::inc(x_42);
lean::dec(x_1);
x_45 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_45, 0, x_36);
lean::cnstr_set(x_45, 1, x_38);
lean::cnstr_set(x_45, 2, x_40);
lean::cnstr_set(x_45, 3, x_32);
lean::cnstr_set(x_45, 4, x_35);
lean::cnstr_set(x_45, 5, x_42);
if (x_2 == 0)
{
obj* x_46; 
x_46 = l_lean_ir_extract__cpp(x_12, x_45);
return x_46;
}
else
{
obj* x_47; obj* x_48; 
x_47 = l_list_map___main___at_lean_ir_lirc___spec__2(x_12);
x_48 = l_lean_ir_extract__cpp(x_47, x_45);
return x_48;
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_list_mmap_x_27___main___at_lean_ir_lirc___spec__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_lirc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_lean_ir_lirc(x_0, x_1, x_3);
return x_4;
}
}
void initialize_init_lean_ir_parser();
void initialize_init_lean_ir_type__check();
void initialize_init_lean_ir_ssa__check();
void initialize_init_lean_ir_extract__cpp();
void initialize_init_lean_ir_format();
void initialize_init_lean_ir_elim__phi();
static bool _G_initialized = false;
void initialize_init_lean_ir_lirc() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_parser();
 initialize_init_lean_ir_type__check();
 initialize_init_lean_ir_ssa__check();
 initialize_init_lean_ir_extract__cpp();
 initialize_init_lean_ir_format();
 initialize_init_lean_ir_elim__phi();
 l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1 = _init_l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1();
lean::mark_persistent(l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1);
}
