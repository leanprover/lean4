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
obj* l_lean_ir_update__external__names___boxed(obj*, obj*, obj*);
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
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2___boxed(obj*, obj*, obj*);
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
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg___boxed(obj*, obj*);
obj* l_lean_ir_update__env___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__fnid2string;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_ir_lirc(obj*, obj*, uint8);
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at_lean_ir_parse__input___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4___boxed(obj*, obj*);
obj* l_lean_ir_extract__cpp(obj*, obj*);
obj* l_lean_parser_parsec_message_to__string___rarg(obj*);
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2___boxed(obj*, obj*, obj*);
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
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_lean_ir_parse__input(obj*);
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1___boxed(obj*, obj*, obj*);
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
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg___boxed), 2, 1);
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
lean::dec(x_17);
x_1 = x_20;
goto lbl_2;
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
x_1 = x_26;
goto lbl_2;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::string_iterator_next(x_0);
x_28 = lean::box(0);
x_29 = lean::box_uint32(x_9);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_28);
x_1 = x_30;
goto lbl_2;
}
}
else
{
if (x_10 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = l_char_quote__core(x_9);
x_32 = l_char_has__repr___closed__1;
x_33 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_35 = lean::string_append(x_33, x_32);
x_36 = lean::box(0);
x_37 = l_mjoin___rarg___closed__1;
x_38 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_35, x_37, x_36, x_36, x_0);
lean::dec(x_0);
lean::dec(x_35);
x_1 = x_38;
goto lbl_2;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::string_iterator_next(x_0);
x_42 = lean::box(0);
x_43 = lean::box_uint32(x_9);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_41);
lean::cnstr_set(x_44, 2, x_42);
x_1 = x_44;
goto lbl_2;
}
}
}
lbl_2:
{
obj* x_45; obj* x_46; 
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_1);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; uint32 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_54 = lean::unbox_uint32(x_47);
x_55 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_54, x_49);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_55);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
x_58 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_59 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_57, x_58);
return x_59;
}
else
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; 
x_60 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_62 = x_46;
} else {
 lean::inc(x_60);
 lean::dec(x_46);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_60, 3);
lean::inc(x_67);
lean::dec(x_60);
x_70 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_63);
lean::cnstr_set(x_71, 1, x_65);
lean::cnstr_set(x_71, 2, x_70);
lean::cnstr_set(x_71, 3, x_67);
x_72 = 0;
if (lean::is_scalar(x_62)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_62;
}
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_72);
x_74 = x_73;
return x_74;
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
x_8 = lean::box(0);
x_11 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_11, 1);
x_14 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_16 = x_11;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_11);
 x_16 = lean::box(0);
}
lean::inc(x_1);
x_18 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_16;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_22);
x_9 = x_23;
goto lbl_10;
}
else
{
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_9 = x_29;
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
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
x_34 = lean::cnstr_get(x_9, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_44; obj* x_46; 
lean::dec(x_9);
x_44 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
x_46 = l_lean_ir_symbol(x_44, x_3);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_52; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 2);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_47);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_55; obj* x_57; obj* x_60; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 2);
lean::inc(x_57);
lean::dec(x_52);
x_60 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_55);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_61 = lean::cnstr_get(x_60, 1);
x_63 = lean::cnstr_get(x_60, 2);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_65 = x_60;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_53);
lean::cnstr_set(x_67, 1, x_61);
lean::cnstr_set(x_67, 2, x_66);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_77; obj* x_78; 
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_69, 2);
lean::inc(x_74);
lean::dec(x_69);
x_77 = l_list_repr___main___rarg___closed__3;
x_78 = l_lean_ir_symbol(x_77, x_72);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_79 = lean::cnstr_get(x_78, 1);
x_81 = lean::cnstr_get(x_78, 2);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_83 = x_78;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_78);
 x_83 = lean::box(0);
}
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_70);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_79);
lean::cnstr_set(x_85, 2, x_66);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_85);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_86);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_87);
x_41 = x_88;
goto lbl_42;
}
else
{
obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_70);
x_90 = lean::cnstr_get(x_78, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (lean::is_exclusive(x_78)) {
 x_93 = x_78;
} else {
 lean::inc(x_90);
 lean::dec(x_78);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_95);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_96);
x_41 = x_97;
goto lbl_42;
}
}
else
{
obj* x_98; uint8 x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::cnstr_get(x_69, 0);
x_100 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_101 = x_69;
} else {
 lean::inc(x_98);
 lean::dec(x_69);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_98);
lean::cnstr_set_scalar(x_102, sizeof(void*)*1, x_100);
x_103 = x_102;
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_103);
x_41 = x_104;
goto lbl_42;
}
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_53);
x_106 = lean::cnstr_get(x_60, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
if (lean::is_exclusive(x_60)) {
 x_109 = x_60;
} else {
 lean::inc(x_106);
 lean::dec(x_60);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = x_110;
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_111);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_115; obj* x_117; obj* x_120; obj* x_121; 
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_112, 2);
lean::inc(x_117);
lean::dec(x_112);
x_120 = l_list_repr___main___rarg___closed__3;
x_121 = l_lean_ir_symbol(x_120, x_115);
if (lean::obj_tag(x_121) == 0)
{
obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_122 = lean::cnstr_get(x_121, 1);
x_124 = lean::cnstr_get(x_121, 2);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_126 = x_121;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_121);
 x_126 = lean::box(0);
}
x_127 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_127, 0, x_113);
x_128 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_126)) {
 x_129 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_129 = x_126;
}
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_122);
lean::cnstr_set(x_129, 2, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_117, x_130);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_131);
x_41 = x_132;
goto lbl_42;
}
else
{
obj* x_134; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_113);
x_134 = lean::cnstr_get(x_121, 0);
x_136 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*1);
if (lean::is_exclusive(x_121)) {
 x_137 = x_121;
} else {
 lean::inc(x_134);
 lean::dec(x_121);
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
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_117, x_139);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_140);
x_41 = x_141;
goto lbl_42;
}
}
else
{
obj* x_142; uint8 x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_142 = lean::cnstr_get(x_112, 0);
x_144 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_exclusive(x_112)) {
 x_145 = x_112;
} else {
 lean::inc(x_142);
 lean::dec(x_112);
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
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_147);
x_41 = x_148;
goto lbl_42;
}
}
}
else
{
obj* x_149; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_149 = lean::cnstr_get(x_52, 0);
x_151 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_exclusive(x_52)) {
 x_152 = x_52;
} else {
 lean::inc(x_149);
 lean::dec(x_52);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_149);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = x_153;
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_154);
x_41 = x_155;
goto lbl_42;
}
}
else
{
obj* x_156; uint8 x_158; obj* x_159; obj* x_160; obj* x_161; 
x_156 = lean::cnstr_get(x_46, 0);
x_158 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 x_159 = x_46;
} else {
 lean::inc(x_156);
 lean::dec(x_46);
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
x_41 = x_161;
goto lbl_42;
}
}
else
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_34);
return x_9;
}
lbl_40:
{
obj* x_167; 
x_167 = l_lean_ir_parse__decl(x_38);
if (lean::obj_tag(x_167) == 0)
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_168; obj* x_170; obj* x_172; obj* x_175; obj* x_176; obj* x_178; obj* x_179; obj* x_180; 
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_167, 2);
lean::inc(x_172);
lean::dec(x_167);
x_175 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_175, 0, x_168);
lean::cnstr_set(x_175, 1, x_1);
x_176 = l_lean_ir_parse__input__aux___main(x_7, x_175, x_2, x_170);
lean::dec(x_7);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_172, x_176);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_178);
x_180 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_179);
return x_180;
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_188; obj* x_192; obj* x_193; obj* x_195; obj* x_198; obj* x_200; obj* x_201; obj* x_202; 
x_181 = lean::cnstr_get(x_167, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_167, 1);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_167, 2);
lean::inc(x_185);
lean::dec(x_167);
x_188 = lean::cnstr_get(x_37, 0);
lean::inc(x_188);
lean::dec(x_37);
lean::inc(x_181);
x_192 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_192, 0, x_181);
lean::cnstr_set(x_192, 1, x_1);
x_193 = l_lean_ir_decl_name(x_181);
lean::dec(x_181);
x_195 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_193, x_188);
lean::dec(x_188);
lean::dec(x_193);
x_198 = l_lean_ir_parse__input__aux___main(x_7, x_192, x_195, x_183);
lean::dec(x_7);
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_185, x_198);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_200);
x_202 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_201);
return x_202;
}
}
else
{
obj* x_207; uint8 x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_37);
x_207 = lean::cnstr_get(x_167, 0);
x_209 = lean::cnstr_get_scalar<uint8>(x_167, sizeof(void*)*1);
if (lean::is_exclusive(x_167)) {
 x_210 = x_167;
} else {
 lean::inc(x_207);
 lean::dec(x_167);
 x_210 = lean::box(0);
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_207);
lean::cnstr_set_scalar(x_211, sizeof(void*)*1, x_209);
x_212 = x_211;
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_212);
x_214 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_213);
return x_214;
}
}
lbl_42:
{
obj* x_215; 
if (lean::obj_tag(x_41) == 0)
{
obj* x_218; 
lean::dec(x_3);
x_218 = lean::box(0);
x_215 = x_218;
goto lbl_216;
}
else
{
obj* x_219; uint8 x_221; 
x_219 = lean::cnstr_get(x_41, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (x_221 == 0)
{
obj* x_223; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_41);
x_223 = lean::cnstr_get(x_219, 2);
lean::inc(x_223);
lean::dec(x_219);
x_226 = l_mjoin___rarg___closed__1;
x_227 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_227, 0, x_223);
lean::closure_set(x_227, 1, x_226);
x_228 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_228, 0, x_227);
x_37 = x_8;
x_38 = x_3;
x_39 = x_228;
goto lbl_40;
}
else
{
obj* x_231; 
lean::dec(x_219);
lean::dec(x_3);
x_231 = lean::box(0);
x_215 = x_231;
goto lbl_216;
}
}
lbl_216:
{
lean::dec(x_215);
if (lean::obj_tag(x_41) == 0)
{
obj* x_233; obj* x_235; obj* x_237; 
x_233 = lean::cnstr_get(x_41, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get(x_41, 1);
lean::inc(x_235);
x_237 = lean::cnstr_get(x_41, 2);
lean::inc(x_237);
lean::dec(x_41);
x_37 = x_233;
x_38 = x_235;
x_39 = x_237;
goto lbl_40;
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_243 = lean::cnstr_get(x_41, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_246 = x_41;
} else {
 lean::inc(x_243);
 lean::dec(x_41);
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
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_248);
return x_249;
}
}
}
}
}
}
else
{
obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
x_250 = l_list_reverse___rarg(x_1);
x_251 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_2);
x_252 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_253 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_253, 0, x_251);
lean::cnstr_set(x_253, 1, x_3);
lean::cnstr_set(x_253, 2, x_252);
return x_253;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_ir_parse__input__aux___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_8 = x_4;
} else {
 lean::inc(x_6);
 lean::dec(x_4);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_11; 
lean::dec(x_4);
x_11 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_14 = x_11;
} else {
 lean::inc(x_12);
 lean::dec(x_11);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
else
{
obj* x_17; 
lean::dec(x_11);
x_17 = l_lean_ir_var_declare___closed__1;
return x_17;
}
}
}
else
{
obj* x_19; 
lean::inc(x_2);
x_19 = l_lean_ir_decl_valid__ssa(x_2);
if (lean::obj_tag(x_19) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_2);
x_21 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_23 = x_19;
} else {
 lean::inc(x_21);
 lean::dec(x_19);
 x_23 = lean::box(0);
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
obj* x_27; 
lean::dec(x_19);
lean::inc(x_2);
x_27 = l_lean_ir_check__blockids(x_2);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
lean::dec(x_2);
x_29 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_31 = x_27;
} else {
 lean::inc(x_29);
 lean::dec(x_27);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
return x_32;
}
else
{
obj* x_34; 
lean::dec(x_27);
x_34 = l_lean_ir_type__check(x_2, x_0);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_34, 0);
if (lean::is_exclusive(x_34)) {
 x_37 = x_34;
} else {
 lean::inc(x_35);
 lean::dec(x_34);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_40; 
lean::dec(x_34);
x_40 = l_lean_ir_var_declare___closed__1;
return x_40;
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
lean::dec(x_0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_lean_ir_decl_name(x_2);
x_5 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_4, x_2);
lean::dec(x_4);
x_0 = x_5;
x_1 = x_3;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::inc(x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
return x_12;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
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
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_lean_ir_update__env___spec__4(x_3, x_0);
x_5 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_4, x_2);
lean::dec(x_4);
x_7 = lean::apply_1(x_1, x_2);
x_8 = l_option_orelse___main___rarg(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
return x_8;
}
}
obj* l_rbnode_ins___main___at_lean_ir_update__env___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_update__env___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_ir_update__env___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_ir_update__env___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_ir_update__env___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_lean_ir_update__env___spec__4(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_update__env___spec__6___rarg(x_0, x_1);
lean::dec(x_0);
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
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_update__env___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_update__env(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::inc(x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
return x_12;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
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
lean::dec(x_0);
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
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_update__external__names___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_update__external__names(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env___boxed), 3, 2);
lean::closure_set(x_15, 0, x_2);
lean::closure_set(x_15, 1, x_12);
x_16 = l_lean_ir_check(x_15, x_1, x_7);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
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
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__env___boxed), 3, 2);
lean::closure_set(x_32, 0, x_12);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::cnstr_get(x_1, 4);
lean::inc(x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_update__external__names___boxed), 3, 2);
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
lean::dec(x_45);
return x_46;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_list_map___main___at_lean_ir_lirc___spec__2(x_12);
x_49 = l_lean_ir_extract__cpp(x_48, x_45);
lean::dec(x_45);
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
lean::mark_persistent(l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1);
}
