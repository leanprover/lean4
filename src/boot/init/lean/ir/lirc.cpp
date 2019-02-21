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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; uint8 x_19; 
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
lean::inc(x_9);
lean::inc(x_1);
x_18 = l_lean_name_quick__lt___main(x_1, x_9);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; uint8 x_23; 
lean::inc(x_1);
lean::inc(x_9);
x_22 = l_lean_name_quick__lt___main(x_9, x_1);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_7);
lean::cnstr_set(x_29, 1, x_9);
lean::cnstr_set(x_29, 2, x_11);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_6);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
lean::cnstr_set(x_32, 2, x_11);
lean::cnstr_set(x_32, 3, x_13);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_6);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; uint8 x_46; 
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
lean::inc(x_36);
lean::inc(x_1);
x_45 = l_lean_name_quick__lt___main(x_1, x_36);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_49; uint8 x_50; 
lean::inc(x_1);
lean::inc(x_36);
x_49 = l_lean_name_quick__lt___main(x_36, x_1);
x_50 = lean::unbox(x_49);
if (x_50 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_38);
lean::dec(x_36);
if (lean::is_scalar(x_42)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_42;
}
lean::cnstr_set(x_53, 0, x_34);
lean::cnstr_set(x_53, 1, x_1);
lean::cnstr_set(x_53, 2, x_2);
lean::cnstr_set(x_53, 3, x_40);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_6);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_56; 
lean::inc(x_40);
x_56 = l_rbnode_is__red___main___rarg(x_40);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_42;
}
lean::cnstr_set(x_61, 0, x_34);
lean::cnstr_set(x_61, 1, x_36);
lean::cnstr_set(x_61, 2, x_38);
lean::cnstr_set(x_61, 3, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_40, x_1, x_2);
x_64 = l_rbnode_balance2___main___rarg(x_62, x_63);
return x_64;
}
}
}
else
{
uint8 x_66; 
lean::inc(x_34);
x_66 = l_rbnode_is__red___main___rarg(x_34);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_42;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_36);
lean::cnstr_set(x_68, 2, x_38);
lean::cnstr_set(x_68, 3, x_40);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_6);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_42;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_36);
lean::cnstr_set(x_71, 2, x_38);
lean::cnstr_set(x_71, 3, x_40);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_6);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_34, x_1, x_2);
x_74 = l_rbnode_balance1___main___rarg(x_72, x_73);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; 
lean::inc(x_0);
x_4 = l_rbnode_is__red___main___rarg(x_0);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_ir_parse__input__aux___main___spec__3(x_0, x_1, x_2);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
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
x_1 = x_7;
goto lbl_2;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_0);
x_9 = l_char_is__alpha(x_8);
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
x_10 = 95;
x_11 = x_8 == x_10;
if (x_11 == 0)
{
if (x_9 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = l_char_quote__core(x_8);
x_13 = l_char_has__repr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_16, x_18, x_17, x_17, x_0);
x_1 = x_19;
goto lbl_2;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::string_iterator_next(x_0);
x_21 = lean::box(0);
x_22 = lean::box_uint32(x_8);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_21);
x_1 = x_23;
goto lbl_2;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::string_iterator_next(x_0);
x_25 = lean::box(0);
x_26 = lean::box_uint32(x_8);
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
if (x_9 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = l_char_quote__core(x_8);
x_29 = l_char_has__repr___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = lean::string_append(x_30, x_29);
x_33 = lean::box(0);
x_34 = l_mjoin___rarg___closed__1;
x_35 = l_lean_parser_monad__parsec_error___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__3___rarg(x_32, x_34, x_33, x_33, x_0);
x_1 = x_35;
goto lbl_2;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::string_iterator_next(x_0);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_8);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_1 = x_39;
goto lbl_2;
}
}
}
lbl_2:
{
obj* x_40; obj* x_41; 
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_1);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_44; obj* x_46; uint32 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 2);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::unbox_uint32(x_42);
x_50 = l_lean_parser_monad__parsec_take__while__cont___at_lean_ir_parse__input__aux___main___spec__5(x_49, x_44);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_50);
x_52 = l_lean_parser_parsec__t_try__mk__res___rarg(x_51);
x_53 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_52, x_53);
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_65; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; 
x_55 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_57 = x_41;
} else {
 lean::inc(x_55);
 lean::dec(x_41);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_55, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_55, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_55, 3);
lean::inc(x_62);
lean::dec(x_55);
x_65 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4___closed__1;
x_66 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_66, 0, x_58);
lean::cnstr_set(x_66, 1, x_60);
lean::cnstr_set(x_66, 2, x_65);
lean::cnstr_set(x_66, 3, x_62);
x_67 = 0;
if (lean::is_scalar(x_57)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_57;
}
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_67);
x_69 = x_68;
return x_69;
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
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_13; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
x_9 = lean::box(0);
lean::inc(x_3);
x_13 = l_lean_parser_monad__parsec_eoi___at___private_init_lean_name__mangling_2__parse__mangled__string__aux___main___spec__6(x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_13, 1);
x_16 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_18 = x_13;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
lean::inc(x_1);
x_20 = l_list_reverse___rarg(x_1);
lean::inc(x_2);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_2);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_18;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_14);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_24);
x_10 = x_25;
goto lbl_11;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_13, 0);
x_28 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_29 = x_13;
} else {
 lean::inc(x_26);
 lean::dec(x_13);
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
x_10 = x_31;
goto lbl_11;
}
lbl_11:
{
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; 
x_36 = lean::cnstr_get(x_10, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_38 == 0)
{
obj* x_46; obj* x_48; 
lean::dec(x_10);
x_46 = l_list_repr___main___rarg___closed__2;
lean::inc(x_3);
x_48 = l_lean_ir_symbol(x_46, x_3);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_54; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 2);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_c__identifier___at_lean_ir_parse__input__aux___main___spec__4(x_49);
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
x_62 = l_lean_parser_monad__parsec_whitespace___at_lean_ir_symbol___spec__2(x_57);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_63 = lean::cnstr_get(x_62, 1);
x_65 = lean::cnstr_get(x_62, 2);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_67 = x_62;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_55);
lean::cnstr_set(x_69, 1, x_63);
lean::cnstr_set(x_69, 2, x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; 
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_71, 2);
lean::inc(x_76);
lean::dec(x_71);
x_79 = l_list_repr___main___rarg___closed__3;
x_80 = l_lean_ir_symbol(x_79, x_74);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_81 = lean::cnstr_get(x_80, 1);
x_83 = lean::cnstr_get(x_80, 2);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_85 = x_80;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_80);
 x_85 = lean::box(0);
}
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_72);
if (lean::is_scalar(x_85)) {
 x_87 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_87 = x_85;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_81);
lean::cnstr_set(x_87, 2, x_68);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_88);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_89);
x_43 = x_90;
goto lbl_44;
}
else
{
obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_72);
x_92 = lean::cnstr_get(x_80, 0);
x_94 = lean::cnstr_get_scalar<uint8>(x_80, sizeof(void*)*1);
if (lean::is_exclusive(x_80)) {
 x_95 = x_80;
} else {
 lean::inc(x_92);
 lean::dec(x_80);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_98);
x_43 = x_99;
goto lbl_44;
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_100 = lean::cnstr_get(x_71, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_103 = x_71;
} else {
 lean::inc(x_100);
 lean::dec(x_71);
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
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_105);
x_43 = x_106;
goto lbl_44;
}
}
else
{
obj* x_108; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_55);
x_108 = lean::cnstr_get(x_62, 0);
x_110 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_exclusive(x_62)) {
 x_111 = x_62;
} else {
 lean::inc(x_108);
 lean::dec(x_62);
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
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_113);
if (lean::obj_tag(x_114) == 0)
{
obj* x_115; obj* x_117; obj* x_119; obj* x_122; obj* x_123; 
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_114, 2);
lean::inc(x_119);
lean::dec(x_114);
x_122 = l_list_repr___main___rarg___closed__3;
x_123 = l_lean_ir_symbol(x_122, x_117);
if (lean::obj_tag(x_123) == 0)
{
obj* x_124; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_124 = lean::cnstr_get(x_123, 1);
x_126 = lean::cnstr_get(x_123, 2);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_128 = x_123;
} else {
 lean::inc(x_124);
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
x_129 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_129, 0, x_115);
x_130 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_128)) {
 x_131 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_131 = x_128;
}
lean::cnstr_set(x_131, 0, x_129);
lean::cnstr_set(x_131, 1, x_124);
lean::cnstr_set(x_131, 2, x_130);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_126, x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_132);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_133);
x_43 = x_134;
goto lbl_44;
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_115);
x_136 = lean::cnstr_get(x_123, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*1);
if (lean::is_exclusive(x_123)) {
 x_139 = x_123;
} else {
 lean::inc(x_136);
 lean::dec(x_123);
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
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_141);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_142);
x_43 = x_143;
goto lbl_44;
}
}
else
{
obj* x_144; uint8 x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_144 = lean::cnstr_get(x_114, 0);
x_146 = lean::cnstr_get_scalar<uint8>(x_114, sizeof(void*)*1);
if (lean::is_exclusive(x_114)) {
 x_147 = x_114;
} else {
 lean::inc(x_144);
 lean::dec(x_114);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_144);
lean::cnstr_set_scalar(x_148, sizeof(void*)*1, x_146);
x_149 = x_148;
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_149);
x_43 = x_150;
goto lbl_44;
}
}
}
else
{
obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_151 = lean::cnstr_get(x_54, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_154 = x_54;
} else {
 lean::inc(x_151);
 lean::dec(x_54);
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
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_156);
x_43 = x_157;
goto lbl_44;
}
}
else
{
obj* x_158; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; 
x_158 = lean::cnstr_get(x_48, 0);
x_160 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_exclusive(x_48)) {
 x_161 = x_48;
} else {
 lean::inc(x_158);
 lean::dec(x_48);
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
x_43 = x_163;
goto lbl_44;
}
}
else
{
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_36);
return x_10;
}
lbl_42:
{
obj* x_169; 
x_169 = l_lean_ir_parse__decl(x_40);
if (lean::obj_tag(x_169) == 0)
{
if (lean::obj_tag(x_39) == 0)
{
obj* x_170; obj* x_172; obj* x_174; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_170 = lean::cnstr_get(x_169, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_169, 1);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_169, 2);
lean::inc(x_174);
lean::dec(x_169);
x_177 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_177, 0, x_170);
lean::cnstr_set(x_177, 1, x_1);
x_178 = l_lean_ir_parse__input__aux___main(x_7, x_177, x_2, x_172);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_178);
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_179);
x_181 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_180);
return x_181;
}
else
{
obj* x_182; obj* x_184; obj* x_186; obj* x_189; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
x_182 = lean::cnstr_get(x_169, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_169, 1);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_169, 2);
lean::inc(x_186);
lean::dec(x_169);
x_189 = lean::cnstr_get(x_39, 0);
lean::inc(x_189);
lean::dec(x_39);
lean::inc(x_182);
x_193 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_193, 0, x_182);
lean::cnstr_set(x_193, 1, x_1);
x_194 = l_lean_ir_decl_name(x_182);
x_195 = l_rbnode_insert___at_lean_ir_parse__input__aux___main___spec__2(x_2, x_194, x_189);
x_196 = l_lean_ir_parse__input__aux___main(x_7, x_193, x_195, x_184);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_186, x_196);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_198);
return x_199;
}
}
else
{
obj* x_204; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_39);
x_204 = lean::cnstr_get(x_169, 0);
x_206 = lean::cnstr_get_scalar<uint8>(x_169, sizeof(void*)*1);
if (lean::is_exclusive(x_169)) {
 x_207 = x_169;
} else {
 lean::inc(x_204);
 lean::dec(x_169);
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
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_209);
x_211 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_210);
return x_211;
}
}
lbl_44:
{
obj* x_212; 
if (lean::obj_tag(x_43) == 0)
{
obj* x_215; 
lean::dec(x_3);
x_215 = lean::box(0);
x_212 = x_215;
goto lbl_213;
}
else
{
obj* x_216; uint8 x_218; 
x_216 = lean::cnstr_get(x_43, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_218 == 0)
{
obj* x_220; obj* x_223; obj* x_224; obj* x_225; 
lean::dec(x_43);
x_220 = lean::cnstr_get(x_216, 2);
lean::inc(x_220);
lean::dec(x_216);
x_223 = l_mjoin___rarg___closed__1;
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_224, 0, x_220);
lean::closure_set(x_224, 1, x_223);
x_225 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_225, 0, x_224);
x_39 = x_9;
x_40 = x_3;
x_41 = x_225;
goto lbl_42;
}
else
{
obj* x_228; 
lean::dec(x_216);
lean::dec(x_3);
x_228 = lean::box(0);
x_212 = x_228;
goto lbl_213;
}
}
lbl_213:
{
lean::dec(x_212);
if (lean::obj_tag(x_43) == 0)
{
obj* x_230; obj* x_232; obj* x_234; 
x_230 = lean::cnstr_get(x_43, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_43, 1);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_43, 2);
lean::inc(x_234);
lean::dec(x_43);
x_39 = x_230;
x_40 = x_232;
x_41 = x_234;
goto lbl_42;
}
else
{
obj* x_240; uint8 x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_240 = lean::cnstr_get(x_43, 0);
x_242 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (lean::is_exclusive(x_43)) {
 x_243 = x_43;
} else {
 lean::inc(x_240);
 lean::dec(x_43);
 x_243 = lean::box(0);
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_240);
lean::cnstr_set_scalar(x_244, sizeof(void*)*1, x_242);
x_245 = x_244;
x_246 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_245);
return x_246;
}
}
}
}
}
}
else
{
obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_0);
x_248 = l_list_reverse___rarg(x_1);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_2);
x_250 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_251 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_251, 0, x_249);
lean::cnstr_set(x_251, 1, x_3);
lean::cnstr_set(x_251, 2, x_250);
return x_251;
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
obj* x_14; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_14);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1, x_16);
x_19 = x_18;
return x_19;
}
}
}
obj* l_lean_ir_parse__input(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::box(0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_parse__input___lambda__1), 3, 2);
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; uint8 x_19; 
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
lean::inc(x_9);
lean::inc(x_1);
x_18 = l_lean_name_quick__lt___main(x_1, x_9);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; uint8 x_23; 
lean::inc(x_1);
lean::inc(x_9);
x_22 = l_lean_name_quick__lt___main(x_9, x_1);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_7);
lean::cnstr_set(x_29, 1, x_9);
lean::cnstr_set(x_29, 2, x_11);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_6);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
lean::cnstr_set(x_32, 2, x_11);
lean::cnstr_set(x_32, 3, x_13);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_6);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; uint8 x_46; 
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
lean::inc(x_36);
lean::inc(x_1);
x_45 = l_lean_name_quick__lt___main(x_1, x_36);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_49; uint8 x_50; 
lean::inc(x_1);
lean::inc(x_36);
x_49 = l_lean_name_quick__lt___main(x_36, x_1);
x_50 = lean::unbox(x_49);
if (x_50 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_38);
lean::dec(x_36);
if (lean::is_scalar(x_42)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_42;
}
lean::cnstr_set(x_53, 0, x_34);
lean::cnstr_set(x_53, 1, x_1);
lean::cnstr_set(x_53, 2, x_2);
lean::cnstr_set(x_53, 3, x_40);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_6);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_56; 
lean::inc(x_40);
x_56 = l_rbnode_is__red___main___rarg(x_40);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_42;
}
lean::cnstr_set(x_61, 0, x_34);
lean::cnstr_set(x_61, 1, x_36);
lean::cnstr_set(x_61, 2, x_38);
lean::cnstr_set(x_61, 3, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_40, x_1, x_2);
x_64 = l_rbnode_balance2___main___rarg(x_62, x_63);
return x_64;
}
}
}
else
{
uint8 x_66; 
lean::inc(x_34);
x_66 = l_rbnode_is__red___main___rarg(x_34);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_42;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_36);
lean::cnstr_set(x_68, 2, x_38);
lean::cnstr_set(x_68, 3, x_40);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_6);
x_69 = x_68;
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_70 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_42;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_36);
lean::cnstr_set(x_71, 2, x_38);
lean::cnstr_set(x_71, 3, x_40);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_6);
x_72 = x_71;
x_73 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_34, x_1, x_2);
x_74 = l_rbnode_balance1___main___rarg(x_72, x_73);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_update__env___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; 
lean::inc(x_0);
x_4 = l_rbnode_is__red___main___rarg(x_0);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_ir_update__env___spec__3(x_0, x_1, x_2);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
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
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
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
if (x_16 == 0)
{
obj* x_19; uint8 x_20; 
lean::dec(x_4);
lean::inc(x_1);
x_19 = l_lean_name_quick__lt___main(x_6, x_1);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_8);
return x_23;
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
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_6);
x_0 = x_4;
goto _start;
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
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
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
if (x_16 == 0)
{
obj* x_19; uint8 x_20; 
lean::dec(x_4);
lean::inc(x_1);
x_19 = l_lean_name_quick__lt___main(x_6, x_1);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_8);
return x_23;
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
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_6);
x_0 = x_4;
goto _start;
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
