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
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_ir_check(obj*, uint8, obj*);
obj* l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_list_reverse___rarg(obj*);
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
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
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
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_update__env(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
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
obj* l_lean_ir_decl_name(obj*);
obj* l_rbmap_find___main___at_lean_ir_update__external__names___spec__1(obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_ir_check___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_whitespace___at_lean_ir_parse__input___spec__1(obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
uint8 l_char_is__alphanum(uint32);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5___boxed(obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_ir_type__check(obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_update__env___spec__5(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
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
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
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
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint32 x_13; uint8 x_14; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
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
lean::dec(x_10);
x_18 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::string_push(x_1, x_13);
x_20 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::string_push(x_1, x_13);
x_23 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_22;
x_2 = x_23;
goto _start;
}
}
else
{
if (x_14 == 0)
{
obj* x_26; 
lean::dec(x_10);
x_26 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::string_push(x_1, x_13);
x_28 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_27;
x_2 = x_28;
goto _start;
}
}
}
}
else
{
obj* x_31; 
lean::dec(x_0);
x_31 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_31;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(uint32 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_0);
x_5 = lean::string_iterator_remaining(x_1);
x_6 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_ir_parse__input__aux___main___spec__6(x_5, x_4, x_1);
return x_6;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_9; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_5, x_6, x_4, x_4, x_0);
x_1 = x_9;
goto lbl_2;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_0);
x_11 = l_char_is__alpha(x_10);
if (x_11 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 95;
x_13 = x_10 == x_12;
if (x_13 == 0)
{
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
x_14 = l_char_quote__core(x_10);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_21);
x_23 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_19, x_21, x_20, x_20, x_0);
x_1 = x_23;
goto lbl_2;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::string_iterator_next(x_0);
x_25 = lean::box(0);
x_26 = lean::box_uint32(x_10);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_25);
x_1 = x_27;
goto lbl_2;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = lean::box_uint32(x_10);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_29);
x_1 = x_31;
goto lbl_2;
}
}
else
{
if (x_11 == 0)
{
obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
x_32 = l_char_quote__core(x_10);
x_33 = l_char_has__repr___closed__1;
lean::inc(x_33);
x_35 = lean::string_append(x_33, x_32);
lean::dec(x_32);
x_37 = lean::string_append(x_35, x_33);
x_38 = lean::box(0);
x_39 = l_mjoin___rarg___closed__1;
lean::inc(x_39);
x_41 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_37, x_39, x_38, x_38, x_0);
x_1 = x_41;
goto lbl_2;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::string_iterator_next(x_0);
x_43 = lean::box(0);
x_44 = lean::box_uint32(x_10);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_42);
lean::cnstr_set(x_45, 2, x_43);
x_1 = x_45;
goto lbl_2;
}
}
}
lbl_2:
{
obj* x_46; obj* x_48; 
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_1);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_53; uint32 x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; 
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 2);
lean::inc(x_53);
lean::dec(x_48);
x_56 = lean::unbox_uint32(x_49);
lean::dec(x_49);
x_58 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_56, x_51);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_58);
x_60 = l_lean_parser_parsec__t_try__mk__res___rarg(x_59);
x_61 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_61);
x_63 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_60, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_76; uint8 x_77; obj* x_78; obj* x_79; 
x_64 = lean::cnstr_get(x_48, 0);
lean::inc(x_64);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_66 = x_48;
}
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_64, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_64, 3);
lean::inc(x_71);
lean::dec(x_64);
x_74 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
lean::inc(x_74);
x_76 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_76, 0, x_67);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_74);
lean::cnstr_set(x_76, 3, x_71);
x_77 = 0;
if (lean::is_scalar(x_66)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_66;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_77);
x_79 = x_78;
return x_79;
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
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_15; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_0, x_7);
lean::dec(x_7);
lean::dec(x_0);
x_11 = lean::box(0);
lean::inc(x_3);
x_15 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 2);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_20 = x_15;
}
lean::inc(x_1);
x_22 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_2);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_16);
lean::cnstr_set(x_27, 2, x_25);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_12 = x_28;
goto lbl_13;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_32 = x_15;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
x_12 = x_34;
goto lbl_13;
}
lbl_13:
{
if (lean::obj_tag(x_12) == 0)
{
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_12;
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; 
x_39 = lean::cnstr_get(x_12, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_41 == 0)
{
obj* x_49; obj* x_52; 
lean::dec(x_12);
x_49 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_49);
x_52 = l_lean_ir_symbol(x_49, x_3);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_52, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 2);
lean::inc(x_55);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 x_57 = x_52;
}
x_58 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_53);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_61; obj* x_63; obj* x_65; obj* x_66; 
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_58, 2);
lean::inc(x_63);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 lean::cnstr_release(x_58, 2);
 x_65 = x_58;
}
x_66 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_61);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_66, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
if (lean::is_scalar(x_57)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_57;
}
lean::cnstr_set(x_74, 0, x_59);
lean::cnstr_set(x_74, 1, x_67);
lean::cnstr_set(x_74, 2, x_72);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_74);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; obj* x_79; obj* x_81; obj* x_84; obj* x_86; 
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_76, 2);
lean::inc(x_81);
lean::dec(x_76);
x_84 = l_list_repr___main___rarg___closed__3;
lean::inc(x_84);
x_86 = l_lean_ir_symbol(x_84, x_79);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_89; obj* x_92; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_87 = lean::cnstr_get(x_86, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 2);
lean::inc(x_89);
lean::dec(x_86);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_77);
lean::inc(x_72);
if (lean::is_scalar(x_65)) {
 x_94 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_94 = x_65;
}
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_87);
lean::cnstr_set(x_94, 2, x_72);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_95);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_96);
x_46 = x_97;
goto lbl_47;
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_65);
lean::dec(x_77);
x_100 = lean::cnstr_get(x_86, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_86, sizeof(void*)*1);
if (lean::is_shared(x_86)) {
 lean::dec(x_86);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_86, 0);
 x_103 = x_86;
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_106);
x_46 = x_107;
goto lbl_47;
}
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_65);
x_109 = lean::cnstr_get(x_76, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get_scalar<uint8>(x_76, sizeof(void*)*1);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_112 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_112 = x_76;
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_114);
x_46 = x_115;
goto lbl_47;
}
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_59);
lean::dec(x_65);
x_118 = lean::cnstr_get(x_66, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_121 = x_66;
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = x_122;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_125; obj* x_127; obj* x_129; obj* x_132; obj* x_134; 
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_124, 2);
lean::inc(x_129);
lean::dec(x_124);
x_132 = l_list_repr___main___rarg___closed__3;
lean::inc(x_132);
x_134 = l_lean_ir_symbol(x_132, x_127);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_137; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_135 = lean::cnstr_get(x_134, 1);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_134, 2);
lean::inc(x_137);
lean::dec(x_134);
x_140 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_140, 0, x_125);
x_141 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_141);
if (lean::is_scalar(x_57)) {
 x_143 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_143 = x_57;
}
lean::cnstr_set(x_143, 0, x_140);
lean::cnstr_set(x_143, 1, x_135);
lean::cnstr_set(x_143, 2, x_141);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_137, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_145);
x_46 = x_146;
goto lbl_47;
}
else
{
obj* x_149; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_125);
lean::dec(x_57);
x_149 = lean::cnstr_get(x_134, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_134, sizeof(void*)*1);
if (lean::is_shared(x_134)) {
 lean::dec(x_134);
 x_152 = lean::box(0);
} else {
 lean::cnstr_release(x_134, 0);
 x_152 = x_134;
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_149);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = x_153;
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_154);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_155);
x_46 = x_156;
goto lbl_47;
}
}
else
{
obj* x_158; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_57);
x_158 = lean::cnstr_get(x_124, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*1);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_161 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_161 = x_124;
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_160);
x_163 = x_162;
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_163);
x_46 = x_164;
goto lbl_47;
}
}
}
else
{
obj* x_166; uint8 x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_57);
x_166 = lean::cnstr_get(x_58, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<uint8>(x_58, sizeof(void*)*1);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_169 = x_58;
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_168);
x_171 = x_170;
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_171);
x_46 = x_172;
goto lbl_47;
}
}
else
{
obj* x_173; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; 
x_173 = lean::cnstr_get(x_52, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_176 = x_52;
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_175);
x_178 = x_177;
x_46 = x_178;
goto lbl_47;
}
}
else
{
lean::dec(x_8);
lean::dec(x_39);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_12;
}
lbl_45:
{
obj* x_184; 
x_184 = l_lean_ir_parse__decl(x_43);
if (lean::obj_tag(x_184) == 0)
{
obj* x_185; obj* x_187; obj* x_189; 
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_184, 2);
lean::inc(x_189);
lean::dec(x_184);
if (lean::obj_tag(x_42) == 0)
{
obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_185);
lean::cnstr_set(x_192, 1, x_1);
x_193 = l_lean_ir_parse__input__aux___main(x_8, x_192, x_2, x_187);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_193);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_194);
x_196 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_195);
return x_196;
}
else
{
obj* x_197; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_197 = lean::cnstr_get(x_42, 0);
lean::inc(x_197);
lean::dec(x_42);
lean::inc(x_185);
x_201 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_201, 0, x_185);
lean::cnstr_set(x_201, 1, x_1);
x_202 = l_lean_ir_decl_name(x_185);
x_203 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_202, x_197);
x_204 = l_lean_ir_parse__input__aux___main(x_8, x_201, x_203, x_187);
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_204);
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_205);
x_207 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_206);
return x_207;
}
}
else
{
obj* x_212; uint8 x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_42);
x_212 = lean::cnstr_get(x_184, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_215 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_215 = x_184;
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set_scalar(x_216, sizeof(void*)*1, x_214);
x_217 = x_216;
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_217);
x_219 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_218);
return x_219;
}
}
lbl_47:
{
obj* x_220; 
if (lean::obj_tag(x_46) == 0)
{
lean::dec(x_3);
x_220 = x_11;
goto lbl_221;
}
else
{
obj* x_223; uint8 x_225; 
x_223 = lean::cnstr_get(x_46, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (x_225 == 0)
{
obj* x_227; obj* x_230; obj* x_232; obj* x_233; 
lean::dec(x_46);
x_227 = lean::cnstr_get(x_223, 2);
lean::inc(x_227);
lean::dec(x_223);
x_230 = l_mjoin___rarg___closed__1;
lean::inc(x_230);
x_232 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_232, 0, x_227);
lean::closure_set(x_232, 1, x_230);
x_233 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_233, 0, x_232);
x_42 = x_11;
x_43 = x_3;
x_44 = x_233;
goto lbl_45;
}
else
{
lean::dec(x_223);
lean::dec(x_3);
x_220 = x_11;
goto lbl_221;
}
}
lbl_221:
{
lean::dec(x_220);
if (lean::obj_tag(x_46) == 0)
{
obj* x_237; obj* x_239; obj* x_241; 
x_237 = lean::cnstr_get(x_46, 0);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_46, 1);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_46, 2);
lean::inc(x_241);
lean::dec(x_46);
x_42 = x_237;
x_43 = x_239;
x_44 = x_241;
goto lbl_45;
}
else
{
obj* x_247; uint8 x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_247 = lean::cnstr_get(x_46, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_250 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_250 = x_46;
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_247);
lean::cnstr_set_scalar(x_251, sizeof(void*)*1, x_249);
x_252 = x_251;
x_253 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_39, x_252);
return x_253;
}
}
}
}
}
}
else
{
obj* x_255; obj* x_256; obj* x_257; obj* x_259; 
lean::dec(x_0);
x_255 = l_list_reverse___rarg(x_1);
x_256 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_256, 0, x_255);
lean::cnstr_set(x_256, 1, x_2);
x_257 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_257);
x_259 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_3);
lean::cnstr_set(x_259, 2, x_257);
return x_259;
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
obj* l_lean_ir_parse__input__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
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
x_8 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_8;
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
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_iterator_next(x_2);
x_18 = 1;
x_0 = x_14;
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
return x_21;
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_ir_mk__fnid2string;
lean::inc(x_9);
x_11 = l_lean_ir_parse__input__aux___main(x_0, x_1, x_9, x_4);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_6, x_11);
return x_12;
}
else
{
obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_18 = x_3;
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
obj* l_lean_ir_parse__input(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_1 = lean::string_length(x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__input___lambda__1), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_3, x_0, x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_9 = x_6;
}
x_10 = l_lean_parser_parsec_message_to__string___rarg(x_7);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
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
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
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
obj* x_11; obj* x_12; 
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
}
x_12 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_11;
 lean::cnstr_set_tag(x_11, 0);
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
else
{
obj* x_19; 
lean::dec(x_11);
lean::dec(x_12);
x_19 = l_lean_ir_var_declare___closed__1;
lean::inc(x_19);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::inc(x_2);
x_22 = l_lean_ir_decl_valid__ssa(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_0);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_27 = x_22;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_31; 
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_29 = x_22;
}
lean::inc(x_2);
x_31 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_31) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_0);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_29)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_39; 
lean::dec(x_31);
x_39 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
lean::dec(x_39);
if (lean::is_scalar(x_29)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_43, 0, x_40);
return x_43;
}
else
{
obj* x_46; 
lean::dec(x_39);
lean::dec(x_29);
x_46 = l_lean_ir_var_declare___closed__1;
lean::inc(x_46);
return x_46;
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
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
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
obj* x_2; obj* x_4; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_8 = l_lean_ir_decl_name(x_2);
x_9 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_8, x_2);
x_0 = x_9;
x_1 = x_4;
goto _start;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::dec(x_4);
lean::inc(x_1);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_10);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_8);
return x_25;
}
else
{
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_43; uint8 x_44; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 3);
lean::inc(x_38);
lean::dec(x_0);
lean::inc(x_34);
lean::inc(x_1);
x_43 = l_lean_name_quick__lt___main(x_1, x_34);
x_44 = lean::unbox(x_43);
lean::dec(x_43);
if (x_44 == 0)
{
obj* x_48; uint8 x_49; 
lean::dec(x_32);
lean::inc(x_1);
x_48 = l_lean_name_quick__lt___main(x_34, x_1);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_53; 
lean::dec(x_1);
lean::dec(x_38);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_36);
return x_53;
}
else
{
lean::dec(x_36);
x_0 = x_38;
goto _start;
}
}
else
{
lean::dec(x_36);
lean::dec(x_38);
lean::dec(x_34);
x_0 = x_32;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg), 2, 0);
return x_2;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_lean_ir_update__env___spec__4(x_3, x_0);
lean::inc(x_2);
x_6 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_4, x_2);
x_7 = lean::apply_1(x_1, x_2);
x_8 = l_option_orelse___main___rarg(x_6, x_7);
return x_8;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::dec(x_4);
lean::inc(x_1);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_10);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_8);
return x_25;
}
else
{
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_43; uint8 x_44; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 3);
lean::inc(x_38);
lean::dec(x_0);
lean::inc(x_34);
lean::inc(x_1);
x_43 = l_lean_name_quick__lt___main(x_1, x_34);
x_44 = lean::unbox(x_43);
lean::dec(x_43);
if (x_44 == 0)
{
obj* x_48; uint8 x_49; 
lean::dec(x_32);
lean::inc(x_1);
x_48 = l_lean_name_quick__lt___main(x_34, x_1);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_53; 
lean::dec(x_1);
lean::dec(x_38);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_36);
return x_53;
}
else
{
lean::dec(x_36);
x_0 = x_38;
goto _start;
}
}
else
{
lean::dec(x_36);
lean::dec(x_38);
lean::dec(x_34);
x_0 = x_32;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_update__external__names___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg), 2, 0);
return x_2;
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
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = l_rbnode_find___main___at_lean_ir_update__external__names___spec__2___rarg(x_0, x_2);
x_5 = lean::apply_1(x_1, x_2);
x_6 = l_option_orelse___main___rarg(x_4, x_5);
return x_6;
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
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::cnstr_get(x_0, 3);
lean::inc(x_13);
lean::inc(x_2);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_16, 0, x_2);
lean::closure_set(x_16, 1, x_13);
x_17 = l_lean_ir_check(x_16, x_1, x_8);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_23 = x_17;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
return x_24;
}
else
{
lean::dec(x_17);
x_3 = x_10;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_5);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
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
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_20; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_11 = x_3;
}
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
obj* x_24; obj* x_27; 
lean::dec(x_1);
lean::dec(x_12);
lean::dec(x_14);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
if (lean::is_scalar(x_11)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_11;
 lean::cnstr_set_tag(x_11, 0);
}
lean::cnstr_set(x_27, 0, x_24);
return x_27;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_46; 
lean::dec(x_11);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_1, 3);
lean::inc(x_30);
lean::inc(x_12);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env), 3, 2);
lean::closure_set(x_33, 0, x_12);
lean::closure_set(x_33, 1, x_30);
x_34 = lean::cnstr_get(x_1, 4);
lean::inc(x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__external__names), 3, 2);
lean::closure_set(x_36, 0, x_14);
lean::closure_set(x_36, 1, x_34);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 2);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 5);
lean::inc(x_43);
lean::dec(x_1);
x_46 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set(x_46, 1, x_39);
lean::cnstr_set(x_46, 2, x_41);
lean::cnstr_set(x_46, 3, x_33);
lean::cnstr_set(x_46, 4, x_36);
lean::cnstr_set(x_46, 5, x_43);
if (x_2 == 0)
{
obj* x_47; 
x_47 = l_lean_ir_extract__cpp(x_12, x_46);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_list_map___main___at_lean_ir_lirc___spec__2(x_12);
x_49 = l_lean_ir_extract__cpp(x_48, x_46);
return x_49;
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
}
