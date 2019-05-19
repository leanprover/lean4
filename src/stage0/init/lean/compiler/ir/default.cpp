// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.borrow init.lean.compiler.ir.boxing init.lean.compiler.ir.rc
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
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
extern obj* l_Lean_IR_tracePrefixOptionName;
extern obj* l_Lean_IR_ExplicitRC_getDecl___closed__1;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_inferBorrow(obj*, obj*, obj*);
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
obj* l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
namespace lean {
namespace ir {
obj* compile_core(obj*, obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
obj* l_Lean_IR_Decl_simpCase___main(obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_IR_explicitRC(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj*, obj*);
obj* l_Lean_IR_explicitBoxing(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
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
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
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
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
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
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
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
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
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
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrow");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrow");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("boxing");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("boxing");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("rc");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("rc");
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
x_59 = l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(x_3, x_49);
x_60 = l_Lean_IR_inferBorrow(x_59, x_1, x_58);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_71; 
x_61 = lean::cnstr_get(x_60, 0);
x_63 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_65 = x_60;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_8);
lean::cnstr_set(x_66, 1, x_63);
x_67 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
x_68 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_1);
lean::inc(x_61);
x_71 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_67, x_68, x_61, x_1, x_66);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_74 = x_71;
} else {
 lean::inc(x_72);
 lean::dec(x_71);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_8);
lean::cnstr_set(x_75, 1, x_72);
x_76 = l_Lean_IR_explicitBoxing(x_61, x_1, x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_87; 
x_77 = lean::cnstr_get(x_76, 0);
x_79 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 x_81 = x_76;
} else {
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_8);
lean::cnstr_set(x_82, 1, x_79);
x_83 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_84 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
lean::inc(x_1);
lean::inc(x_77);
x_87 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_83, x_84, x_77, x_1, x_82);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
x_88 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_90 = x_87;
} else {
 lean::inc(x_88);
 lean::dec(x_87);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_8);
lean::cnstr_set(x_91, 1, x_88);
x_92 = l_Lean_IR_explicitRC(x_77, x_1, x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_103; 
x_93 = lean::cnstr_get(x_92, 0);
x_95 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 x_97 = x_92;
} else {
 lean::inc(x_93);
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_8);
lean::cnstr_set(x_98, 1, x_95);
x_99 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
x_100 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
lean::inc(x_1);
lean::inc(x_93);
x_103 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_99, x_100, x_93, x_1, x_98);
if (lean::obj_tag(x_103) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
x_104 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_106 = x_103;
} else {
 lean::inc(x_104);
 lean::dec(x_103);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_8);
lean::cnstr_set(x_107, 1, x_104);
x_108 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_93, x_3, x_1, x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_111; obj* x_112; obj* x_113; 
x_109 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_111 = x_108;
} else {
 lean::inc(x_109);
 lean::dec(x_108);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_8);
lean::cnstr_set(x_112, 1, x_109);
x_113 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_93, x_3, x_1, x_112);
lean::dec(x_1);
lean::dec(x_93);
if (lean::obj_tag(x_113) == 0)
{
obj* x_116; obj* x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_113, 1);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 x_118 = x_113;
} else {
 lean::inc(x_116);
 lean::dec(x_113);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_8);
lean::cnstr_set(x_119, 1, x_116);
return x_119;
}
else
{
obj* x_120; obj* x_122; obj* x_124; obj* x_125; 
x_120 = lean::cnstr_get(x_113, 0);
x_122 = lean::cnstr_get(x_113, 1);
if (lean::is_exclusive(x_113)) {
 x_124 = x_113;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_113);
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
lean::dec(x_93);
x_128 = lean::cnstr_get(x_108, 0);
x_130 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 x_132 = x_108;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_108);
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
else
{
obj* x_136; obj* x_138; obj* x_140; obj* x_141; 
lean::dec(x_1);
lean::dec(x_93);
x_136 = lean::cnstr_get(x_103, 0);
x_138 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_140 = x_103;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::dec(x_103);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_136);
lean::cnstr_set(x_141, 1, x_138);
return x_141;
}
}
else
{
obj* x_143; obj* x_145; obj* x_147; obj* x_148; 
lean::dec(x_1);
x_143 = lean::cnstr_get(x_92, 0);
x_145 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 x_147 = x_92;
} else {
 lean::inc(x_143);
 lean::inc(x_145);
 lean::dec(x_92);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_143);
lean::cnstr_set(x_148, 1, x_145);
return x_148;
}
}
else
{
obj* x_151; obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_1);
lean::dec(x_77);
x_151 = lean::cnstr_get(x_87, 0);
x_153 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 x_155 = x_87;
} else {
 lean::inc(x_151);
 lean::inc(x_153);
 lean::dec(x_87);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_151);
lean::cnstr_set(x_156, 1, x_153);
return x_156;
}
}
else
{
obj* x_158; obj* x_160; obj* x_162; obj* x_163; 
lean::dec(x_1);
x_158 = lean::cnstr_get(x_76, 0);
x_160 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 x_162 = x_76;
} else {
 lean::inc(x_158);
 lean::inc(x_160);
 lean::dec(x_76);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_158);
lean::cnstr_set(x_163, 1, x_160);
return x_163;
}
}
else
{
obj* x_166; obj* x_168; obj* x_170; obj* x_171; 
lean::dec(x_1);
lean::dec(x_61);
x_166 = lean::cnstr_get(x_71, 0);
x_168 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_170 = x_71;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_71);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_168);
return x_171;
}
}
else
{
obj* x_173; obj* x_175; obj* x_177; obj* x_178; 
lean::dec(x_1);
x_173 = lean::cnstr_get(x_60, 0);
x_175 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_177 = x_60;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_60);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_173);
lean::cnstr_set(x_178, 1, x_175);
return x_178;
}
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_1);
lean::dec(x_49);
x_181 = lean::cnstr_get(x_54, 0);
x_183 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_185 = x_54;
} else {
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_54);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_181);
lean::cnstr_set(x_186, 1, x_183);
return x_186;
}
}
else
{
obj* x_189; obj* x_191; obj* x_193; obj* x_194; 
lean::dec(x_1);
lean::dec(x_39);
x_189 = lean::cnstr_get(x_44, 0);
x_191 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_193 = x_44;
} else {
 lean::inc(x_189);
 lean::inc(x_191);
 lean::dec(x_44);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_189);
lean::cnstr_set(x_194, 1, x_191);
return x_194;
}
}
else
{
obj* x_197; obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_1);
lean::dec(x_29);
x_197 = lean::cnstr_get(x_34, 0);
x_199 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 x_201 = x_34;
} else {
 lean::inc(x_197);
 lean::inc(x_199);
 lean::dec(x_34);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_197);
lean::cnstr_set(x_202, 1, x_199);
return x_202;
}
}
else
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_1);
lean::dec(x_19);
x_205 = lean::cnstr_get(x_24, 0);
x_207 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_209 = x_24;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_24);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_205);
lean::cnstr_set(x_210, 1, x_207);
return x_210;
}
}
else
{
obj* x_213; obj* x_215; obj* x_217; obj* x_218; 
lean::dec(x_1);
lean::dec(x_0);
x_213 = lean::cnstr_get(x_14, 0);
x_215 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_217 = x_14;
} else {
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_14);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_213);
lean::cnstr_set(x_218, 1, x_215);
return x_218;
}
}
else
{
obj* x_221; obj* x_223; obj* x_225; obj* x_226; 
lean::dec(x_1);
lean::dec(x_0);
x_221 = lean::cnstr_get(x_4, 0);
x_223 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_225 = x_4;
} else {
 lean::inc(x_221);
 lean::inc(x_223);
 lean::dec(x_4);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_221);
lean::cnstr_set(x_226, 1, x_223);
return x_226;
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
obj* initialize_init_lean_compiler_ir_borrow(obj*);
obj* initialize_init_lean_compiler_ir_boxing(obj*);
obj* initialize_init_lean_compiler_ir_rc(obj*);
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
w = initialize_init_lean_compiler_ir_borrow(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_rc(w);
if (io_result_is_error(w)) return w;
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
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__11 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__11);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__12 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__12);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__13 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__13);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__14 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__14);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__15 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__15);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__16 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__16);
return w;
}
