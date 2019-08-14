// Lean compiler output
// Module: init.lean.elaborator.term
// Imports: init.lean.elaborator.alias init.lean.elaborator.basic
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
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elab_elabTerm___closed__2;
obj* l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2(obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_termElabAttribute;
obj* l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2___boxed(obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_Elab_elabTerm___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1(obj*, obj*);
obj* l_Lean_Elab_elabTerm___closed__3;
obj* l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3___boxed(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Elab_elabTerm(obj*, obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Elab_logErrorAndThrow___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; 
lean::inc(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_5);
return x_9;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2(x_8, x_2);
return x_9;
}
}
}
obj* _init_l_Lean_Elab_elabTerm___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabTerm___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabTerm___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_elabTerm___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term elaborator failed, no support for syntax '");
return x_1;
}
}
obj* l_Lean_Elab_elabTerm(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::inc(x_6);
lean::cnstr_set(x_3, 0, x_8);
x_9 = l_Lean_termElabAttribute;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_12 = l_Lean_PersistentEnvExtension_getState___rarg(x_10, x_11);
lean::dec(x_11);
x_13 = l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1(x_12, x_4);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_4);
x_16 = l_Lean_Elab_elabTerm___closed__3;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_19, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_22 = lean::apply_3(x_21, x_1, x_2, x_3);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::dec(x_3);
x_24 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = l_Lean_termElabAttribute;
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_29 = l_Lean_PersistentEnvExtension_getState___rarg(x_27, x_28);
lean::dec(x_28);
x_30 = l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1(x_29, x_4);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = l_Lean_Name_toString___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_4);
x_33 = l_Lean_Elab_elabTerm___closed__3;
x_34 = lean::string_append(x_33, x_32);
lean::dec(x_32);
x_35 = l_Char_HasRepr___closed__1;
x_36 = lean::string_append(x_34, x_35);
x_37 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_36, x_2, x_25);
lean::dec(x_2);
lean::dec(x_1);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_4);
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_39 = lean::apply_3(x_38, x_1, x_2, x_25);
return x_39;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_2);
lean::dec(x_1);
x_40 = !lean::is_exclusive(x_3);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_3, 0);
lean::dec(x_41);
x_42 = l_Lean_Elab_elabTerm___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_42);
return x_3;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_3, 1);
lean::inc(x_43);
lean::dec(x_3);
x_44 = l_Lean_Elab_elabTerm___closed__2;
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_elabTerm___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_elabTerm___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_Elab_elabTerm___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_elaborator_alias(obj*);
obj* initialize_init_lean_elaborator_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_term(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (io_result_is_error(w)) return w;
l_Lean_Elab_elabTerm___closed__1 = _init_l_Lean_Elab_elabTerm___closed__1();
lean::mark_persistent(l_Lean_Elab_elabTerm___closed__1);
l_Lean_Elab_elabTerm___closed__2 = _init_l_Lean_Elab_elabTerm___closed__2();
lean::mark_persistent(l_Lean_Elab_elabTerm___closed__2);
l_Lean_Elab_elabTerm___closed__3 = _init_l_Lean_Elab_elabTerm___closed__3();
lean::mark_persistent(l_Lean_Elab_elabTerm___closed__3);
return w;
}
