// Lean compiler output
// Module: init.lean.elaborator.resolvename
// Imports: init.default init.lean.modifiers init.lean.elaborator.alias init.lean.elaborator.basic
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
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elab_preresolveNames___rarg(obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_Elab_preresolveNames(obj*);
obj* l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_preresolveNames___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main(obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_Name_isAtomic(obj*);
obj* l_Lean_getAliases(obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_getNamespace___rarg(obj*);
obj* l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_List_append___rarg(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_3__resolveExact___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_resolveName___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Elab_rootNamespace;
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_getEnv___rarg(obj*);
obj* l_Lean_Elab_resolveName(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_3__resolveExact(obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace(obj*, obj*, obj*);
uint8 l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(obj*, obj*);
obj* l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__1(obj*, obj*);
obj* l_Lean_Elab_getOpenDecls___rarg(obj*);
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux(obj*);
namespace lean {
uint8 is_protected_core(obj*, obj*);
}
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName___boxed(obj*, obj*, obj*);
obj* l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__2(obj*, obj*);
uint8 l_Lean_Environment_contains(obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1(obj*);
obj* l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
lean::inc(x_3);
x_4 = l_Lean_Name_append___main(x_2, x_3);
x_5 = l_Lean_getAliases(x_1, x_4);
x_6 = l_Lean_Environment_contains(x_1, x_4);
if (x_6 == 0)
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
else
{
uint8 x_7; 
x_7 = l_Lean_Name_isAtomic(x_3);
lean::dec(x_3);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8 x_9; 
lean::inc(x_4);
x_9 = lean::is_protected_core(x_1, x_4);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_5);
return x_10;
}
else
{
lean::dec(x_4);
return x_5;
}
}
}
}
}
obj* l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 1)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName(x_1, x_3, x_2);
if (lean::obj_tag(x_5) == 0)
{
x_3 = x_4;
goto _start;
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
else
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::box(0);
return x_7;
}
}
}
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_lean_elaborator_resolvename_3__resolveExact(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Name_isAtomic(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = l_Lean_Elab_rootNamespace;
x_5 = lean::box(0);
x_6 = l_Lean_Name_replacePrefix___main(x_2, x_4, x_5);
x_7 = l_Lean_Environment_contains(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
}
else
{
obj* x_10; 
lean::dec(x_2);
x_10 = lean::box(0);
return x_10;
}
}
}
obj* l___private_init_lean_elaborator_resolvename_3__resolveExact___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_elaborator_resolvename_3__resolveExact(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_2, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_10 = l___private_init_lean_elaborator_resolvename_1__resolveQualifiedName(x_1, x_7, x_2);
lean::dec(x_7);
x_11 = l_List_append___rarg(x_10, x_4);
x_3 = x_6;
x_4 = x_11;
goto _start;
}
else
{
lean::dec(x_7);
x_3 = x_6;
goto _start;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_3);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_15 = lean::cnstr_get(x_3, 1);
x_16 = lean::cnstr_get(x_3, 0);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_19 = lean_name_dec_eq(x_2, x_17);
lean::dec(x_17);
if (x_19 == 0)
{
lean::dec(x_18);
lean::free_heap_obj(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean::cnstr_set(x_3, 1, x_4);
lean::cnstr_set(x_3, 0, x_18);
{
obj* _tmp_2 = x_15;
obj* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
lean::dec(x_3);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_5, 1);
lean::inc(x_24);
lean::dec(x_5);
x_25 = lean_name_dec_eq(x_2, x_23);
lean::dec(x_23);
if (x_25 == 0)
{
lean::dec(x_24);
x_3 = x_22;
goto _start;
}
else
{
obj* x_27; 
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_4);
x_3 = x_22;
x_4 = x_27;
goto _start;
}
}
}
}
}
}
obj* l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__1(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__1(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__2(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__2(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_4) == 1)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::inc(x_4);
lean::inc(x_1);
x_7 = l___private_init_lean_elaborator_resolvename_2__resolveUsingNamespace___main(x_1, x_4, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
lean::inc(x_4);
x_8 = l___private_init_lean_elaborator_resolvename_3__resolveExact(x_1, x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; obj* x_10; obj* x_11; 
x_9 = l_Lean_Environment_contains(x_1, x_4);
x_10 = l_Lean_getAliases(x_1, x_4);
if (x_9 == 0)
{
obj* x_18; obj* x_19; 
lean::inc(x_3);
lean::inc(x_1);
x_18 = l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls___main(x_1, x_4, x_3, x_7);
x_19 = l_List_append___rarg(x_10, x_18);
x_11 = x_19;
goto block_17;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::inc(x_4);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_7);
lean::inc(x_3);
lean::inc(x_1);
x_21 = l___private_init_lean_elaborator_resolvename_4__resolveOpenDecls___main(x_1, x_4, x_3, x_20);
x_22 = l_List_append___rarg(x_10, x_21);
x_11 = x_22;
goto block_17;
}
block_17:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_5, x_12);
lean::dec(x_5);
x_4 = x_6;
x_5 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_15 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_11);
x_16 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__1(x_5, x_15);
return x_16;
}
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_8, 0);
lean::inc(x_23);
lean::dec(x_8);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_27 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_7);
x_28 = l_List_map___main___at___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___spec__2(x_5, x_27);
return x_28;
}
}
else
{
obj* x_29; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_29 = lean::box(0);
return x_29;
}
}
}
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_elaborator_resolvename_5__resolveNameAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Elab_resolveName(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getEnv___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = l_Lean_Elab_getNamespace___rarg(x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_8, 0);
lean::cnstr_set(x_8, 0, x_7);
x_11 = l_Lean_Elab_getOpenDecls___rarg(x_8);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = lean::mk_nat_obj(0u);
x_15 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_6, x_10, x_13, x_1, x_14);
lean::dec(x_10);
lean::cnstr_set(x_11, 0, x_15);
return x_11;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_11, 0);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_11);
x_18 = lean::mk_nat_obj(0u);
x_19 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_6, x_10, x_16, x_1, x_18);
lean::dec(x_10);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_11, 0);
x_23 = lean::cnstr_get(x_11, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_11);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_8, 0);
x_26 = lean::cnstr_get(x_8, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_8);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_getOpenDecls___rarg(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_31 = x_28;
} else {
 lean::dec_ref(x_28);
 x_31 = lean::box(0);
}
x_32 = lean::mk_nat_obj(0u);
x_33 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_6, x_25, x_29, x_1, x_32);
lean::dec(x_25);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_25);
lean::dec(x_6);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_28, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_37 = x_28;
} else {
 lean::dec_ref(x_28);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8 x_39; 
lean::dec(x_6);
lean::dec(x_1);
x_39 = !lean::is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_8, 0);
x_41 = lean::cnstr_get(x_8, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_8);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_43 = lean::cnstr_get(x_4, 0);
x_44 = lean::cnstr_get(x_4, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_4);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_getNamespace___rarg(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_47, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_50 = x_47;
} else {
 lean::dec_ref(x_47);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_getOpenDecls___rarg(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_55 = x_52;
} else {
 lean::dec_ref(x_52);
 x_55 = lean::box(0);
}
x_56 = lean::mk_nat_obj(0u);
x_57 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_43, x_48, x_53, x_1, x_56);
lean::dec(x_48);
if (lean::is_scalar(x_55)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_55;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_54);
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_48);
lean::dec(x_43);
lean::dec(x_1);
x_59 = lean::cnstr_get(x_52, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_52, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_61 = x_52;
} else {
 lean::dec_ref(x_52);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_60);
return x_62;
}
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_43);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_47, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_47, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_65 = x_47;
} else {
 lean::dec_ref(x_47);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8 x_67; 
lean::dec(x_1);
x_67 = !lean::is_exclusive(x_4);
if (x_67 == 0)
{
return x_4;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_4, 0);
x_69 = lean::cnstr_get(x_4, 1);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_4);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
}
}
}
obj* l_Lean_Elab_resolveName___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveName(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::array_fget(x_5, x_4);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = x_11;
x_13 = lean::array_fset(x_5, x_4, x_12);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_1);
x_14 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_10);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_4, x_15);
x_17 = x_14;
x_18 = lean::array_fset(x_13, x_4, x_17);
lean::dec(x_4);
x_4 = x_16;
x_5 = x_18;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_4)) {
case 1:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_7, x_6);
lean::cnstr_set(x_4, 1, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_4);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
case 3:
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_4);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_4, 2);
x_16 = lean::cnstr_get(x_4, 3);
lean::dec(x_16);
x_17 = lean::mk_nat_obj(0u);
lean::inc(x_15);
x_18 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_1, x_2, x_3, x_15, x_17);
lean::cnstr_set(x_4, 3, x_18);
return x_4;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_4, 0);
x_20 = lean::cnstr_get(x_4, 1);
x_21 = lean::cnstr_get(x_4, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_4);
x_22 = lean::mk_nat_obj(0u);
lean::inc(x_21);
x_23 = l___private_init_lean_elaborator_resolvename_5__resolveNameAux___main(x_1, x_2, x_3, x_21, x_22);
x_24 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set(x_24, 2, x_21);
lean::cnstr_set(x_24, 3, x_23);
return x_24;
}
}
default: 
{
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_ummapAux___main___at___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Elab_preresolveNames___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getEnv___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = l_Lean_Elab_getNamespace___rarg(x_4);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_8, 0);
lean::cnstr_set(x_8, 0, x_7);
x_11 = l_Lean_Elab_getOpenDecls___rarg(x_8);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_6, x_10, x_13, x_1);
lean::dec(x_10);
lean::cnstr_set(x_11, 0, x_14);
return x_11;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_11, 0);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_11);
x_17 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_6, x_10, x_15, x_1);
lean::dec(x_10);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8 x_19; 
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_1);
x_19 = !lean::is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_11, 0);
x_21 = lean::cnstr_get(x_11, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_8, 0);
x_24 = lean::cnstr_get(x_8, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_8);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_getOpenDecls___rarg(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_29 = x_26;
} else {
 lean::dec_ref(x_26);
 x_29 = lean::box(0);
}
x_30 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_6, x_23, x_27, x_1);
lean::dec(x_23);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_23);
lean::dec(x_6);
lean::dec(x_1);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_34 = x_26;
} else {
 lean::dec_ref(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8 x_36; 
lean::dec(x_6);
lean::dec(x_1);
x_36 = !lean::is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_8, 0);
x_38 = lean::cnstr_get(x_8, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_8);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_4, 0);
x_41 = lean::cnstr_get(x_4, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_4);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_getNamespace___rarg(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_42);
lean::cnstr_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_getOpenDecls___rarg(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = l___private_init_lean_elaborator_resolvename_6__preresolveNamesAux___main___rarg(x_40, x_45, x_50, x_1);
lean::dec(x_45);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_45);
lean::dec(x_40);
lean::dec(x_1);
x_55 = lean::cnstr_get(x_49, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_49, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_57 = x_49;
} else {
 lean::dec_ref(x_49);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set(x_58, 1, x_56);
return x_58;
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_40);
lean::dec(x_1);
x_59 = lean::cnstr_get(x_44, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_44, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_61 = x_44;
} else {
 lean::dec_ref(x_44);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8 x_63; 
lean::dec(x_1);
x_63 = !lean::is_exclusive(x_4);
if (x_63 == 0)
{
return x_4;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = lean::cnstr_get(x_4, 0);
x_65 = lean::cnstr_get(x_4, 1);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_4);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
}
}
}
obj* l_Lean_Elab_preresolveNames(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_preresolveNames___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Elab_preresolveNames___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_preresolveNames___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_modifiers(obj*);
obj* initialize_init_lean_elaborator_alias(obj*);
obj* initialize_init_lean_elaborator_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_resolvename(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_modifiers(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (io_result_is_error(w)) return w;
return w;
}
