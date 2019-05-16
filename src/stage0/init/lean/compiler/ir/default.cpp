// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.boxing
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
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
obj* l_Lean_IR_Decl_pushProj___main(obj*);
extern obj* l_Lean_IR_tracePrefixOptionName;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
namespace lean {
namespace ir {
obj* compile_core(obj*, obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
obj* l_Lean_IR_Decl_simpCase___main(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj*, obj*);
obj* _init_l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
x_2 = lean::box(0);
x_3 = 6;
x_4 = lean::alloc_cnstr(1, 2, 1);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_3);
x_5 = x_4;
return x_5;
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_pushProj___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_insertResetReuse___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_elimDead___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_simpCase___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_normalizeIds(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("init");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("init");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("push_proj");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("push_proj");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("elim_dead");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("elim_dead");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("simp_case");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("simp_case");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_0, x_3, x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; 
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
x_11 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_14 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_10, x_11, x_0, x_1, x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; 
x_15 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_17 = x_14;
} else {
 lean::inc(x_15);
 lean::dec(x_14);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_15);
x_19 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_3, x_0);
x_20 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
x_21 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
lean::inc(x_1);
lean::inc(x_19);
x_24 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_20, x_21, x_19, x_1, x_18);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_34; 
x_25 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_27 = x_24;
} else {
 lean::inc(x_25);
 lean::dec(x_24);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_8);
lean::cnstr_set(x_28, 1, x_25);
x_29 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_3, x_19);
x_30 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
x_31 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_1);
lean::inc(x_29);
x_34 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_30, x_31, x_29, x_1, x_28);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_44; 
x_35 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_37 = x_34;
} else {
 lean::inc(x_35);
 lean::dec(x_34);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_35);
x_39 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_3, x_29);
x_40 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_41 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
lean::inc(x_1);
lean::inc(x_39);
x_44 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_40, x_41, x_39, x_1, x_38);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_54; 
x_45 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_47 = x_44;
} else {
 lean::inc(x_45);
 lean::dec(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_8);
lean::cnstr_set(x_48, 1, x_45);
x_49 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_3, x_39);
x_50 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
x_51 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
lean::inc(x_1);
lean::inc(x_49);
x_54 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_50, x_51, x_49, x_1, x_48);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_57 = x_54;
} else {
 lean::inc(x_55);
 lean::dec(x_54);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_8);
lean::cnstr_set(x_58, 1, x_55);
x_59 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_3, x_49);
x_60 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_59, x_3, x_1, x_58);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_63 = x_60;
} else {
 lean::inc(x_61);
 lean::dec(x_60);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_8);
lean::cnstr_set(x_64, 1, x_61);
x_65 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_59, x_3, x_1, x_64);
lean::dec(x_1);
lean::dec(x_59);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
x_68 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 x_70 = x_65;
} else {
 lean::inc(x_68);
 lean::dec(x_65);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_8);
lean::cnstr_set(x_71, 1, x_68);
return x_71;
}
else
{
obj* x_72; obj* x_74; obj* x_76; obj* x_77; 
x_72 = lean::cnstr_get(x_65, 0);
x_74 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 x_76 = x_65;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_65);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_72);
lean::cnstr_set(x_77, 1, x_74);
return x_77;
}
}
else
{
obj* x_80; obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_59);
x_80 = lean::cnstr_get(x_60, 0);
x_82 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_84 = x_60;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_60);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_80);
lean::cnstr_set(x_85, 1, x_82);
return x_85;
}
}
else
{
obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_1);
lean::dec(x_49);
x_88 = lean::cnstr_get(x_54, 0);
x_90 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_92 = x_54;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_54);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_88);
lean::cnstr_set(x_93, 1, x_90);
return x_93;
}
}
else
{
obj* x_96; obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_1);
lean::dec(x_39);
x_96 = lean::cnstr_get(x_44, 0);
x_98 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_100 = x_44;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_44);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_96);
lean::cnstr_set(x_101, 1, x_98);
return x_101;
}
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_1);
lean::dec(x_29);
x_104 = lean::cnstr_get(x_34, 0);
x_106 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 x_108 = x_34;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_34);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set(x_109, 1, x_106);
return x_109;
}
}
else
{
obj* x_112; obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_1);
lean::dec(x_19);
x_112 = lean::cnstr_get(x_24, 0);
x_114 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_116 = x_24;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_24);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_112);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
else
{
obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_1);
lean::dec(x_0);
x_120 = lean::cnstr_get(x_14, 0);
x_122 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_124 = x_14;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_14);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_120);
lean::cnstr_set(x_125, 1, x_122);
return x_125;
}
}
else
{
obj* x_128; obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_1);
lean::dec(x_0);
x_128 = lean::cnstr_get(x_4, 0);
x_130 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_132 = x_4;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_4);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_128);
lean::cnstr_set(x_133, 1, x_130);
return x_133;
}
}
}
namespace lean {
namespace ir {
obj* compile_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Array_empty___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = l___private_init_lean_compiler_ir_default_1__compileAux(x_2, x_1, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_23; obj* x_26; obj* x_27; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_7, 1);
lean::inc(x_20);
lean::dec(x_7);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_18);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
}}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_pushproj(obj*);
obj* initialize_init_lean_compiler_ir_elimdead(obj*);
obj* initialize_init_lean_compiler_ir_simpcase(obj*);
obj* initialize_init_lean_compiler_ir_resetreuse(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
obj* initialize_init_lean_compiler_ir_checker(obj*);
obj* initialize_init_lean_compiler_ir_boxing(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_pushproj(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_resetreuse(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_checker(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1___closed__1);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__1 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__1);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__2 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__2);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__3 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__3);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__4 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__4);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__5 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__5);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__6 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__6);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__7 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__7);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__8 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__8);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__9 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__9);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__10 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__10);
return w;
}
