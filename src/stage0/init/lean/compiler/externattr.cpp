// Lean compiler output
// Module: init.lean.compiler.externattr
// Imports: init.data.option.basic init.lean.expr init.lean.environment init.lean.attributes init.lean.projfns
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
obj* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2___boxed(obj*, obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l_Lean_getExternEntryForAux___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(obj*, obj*);
namespace lean {
obj* mk_extern_attr_data_core(obj*, obj*);
}
obj* l_Lean_expandExternPatternAux(obj*, obj*, obj*, obj*);
obj* l_Lean_getExternNameFor(obj*, obj*, obj*);
obj* l_Lean_getExternNameFor___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_ExternEntry_backend(obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__4___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries(obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3___boxed(obj*, obj*, obj*);
extern obj* l_Lean_stxInh;
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5;
namespace lean {
obj* mk_adhoc_ext_entry_core(obj*);
}
obj* l_Lean_addExtern___boxed(obj*, obj*);
namespace lean {
obj* mk_foreign_ext_entry_core(obj*, obj*);
}
obj* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(obj*, obj*, obj*);
obj* l_List_intersperse___main___rarg(obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_expandExternEntry(obj*, obj*);
obj* l_Lean_getExternAttrDataOld___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__1___boxed(obj*);
obj* l_List_getOpt___main___rarg(obj*, obj*);
obj* l_Lean_mkProjectionFnInfoExtension___lambda__2___boxed(obj*);
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(obj*, obj*);
obj* l_Lean_ExternEntry_backend___main___boxed(obj*);
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Lean_expandExternEntry___main(obj*, obj*);
obj* l_Lean_mkExternAttr___closed__2;
namespace lean {
obj* mk_extern_call_core(obj*, obj*, obj*);
}
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1;
obj* l_Lean_mkExternAttr___closed__3;
obj* l_String_Iterator_remainingBytes___main(obj*);
obj* l_Lean_mkExternAttr___lambda__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1;
obj* l_Lean_isExtern___boxed(obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2;
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_3__parseOptNum___main(obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_mkExternAttr___closed__1;
obj* l_Array_swap(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
obj* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___boxed(obj*);
obj* l_Lean_Syntax_isStrLit___main(obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__5(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_ExternEntry_backend___boxed(obj*);
obj* l_Lean_expandExternPatternAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(obj*);
namespace lean {
obj* expand_extern_pattern_core(obj*, obj*);
}
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
obj* l_Lean_Syntax_isNatLit___main(obj*);
obj* l_String_Iterator_next___main(obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* get_extern_attr_data_core(obj*, obj*);
}
uint8 l_Lean_Environment_isConstructor(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
uint8 l_UInt32_decLe(uint32, uint32);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_Lean_expandExternPatternAux___main___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_registerParametricAttribute___rarg___closed__2;
extern obj* l_Option_HasRepr___rarg___closed__3;
uint8 l_Lean_isExtern(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Lean_isExternC(obj*, obj*);
extern obj* l_Lean_registerTagAttribute___closed__6;
obj* l_Lean_expandExternPatternAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Environment_isProjectionFn(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(obj*, obj*, obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_externAttr;
obj* l_Lean_mkProjectionFnInfoExtension___lambda__1(obj*, obj*);
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3;
obj* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_compiler_externattr_3__parseOptNum(obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
namespace lean {
obj* mk_inline_ext_entry_core(obj*, obj*);
}
obj* l_Lean_registerParametricAttribute___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1;
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2___boxed(obj*);
obj* l_Lean_mkExternAttr(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_getExternEntryForAux(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_getExternEntryForAux___main___boxed(obj*, obj*);
obj* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3;
uint8 l_String_Iterator_hasNext___main(obj*);
extern obj* l_Lean_registerTagAttribute___closed__5;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(obj*, obj*);
obj* l_Lean_getExternEntryForAux___main(obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
namespace lean {
obj* get_extern_entry_for_core(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2;
obj* l_Lean_mkExternAttr___lambda__1(obj*, obj*, obj*);
obj* l_Lean_AttributeImpl_inhabited___lambda__2___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* mk_std_ext_entry_core(obj*, obj*);
}
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData(obj*);
extern "C" obj* lean_add_extern(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___boxed(obj*, obj*, obj*);
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed(obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_Syntax_isIdOrAtom___main(obj*);
extern "C" obj* lean_get_extern_attr_data(obj*, obj*);
obj* l_Lean_ExternEntry_backend___main(obj*);
obj* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4;
obj* l_Lean_isExternC___boxed(obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_ExternAttrData_inhabited;
obj* l_Lean_mkSimpleFnCall(obj*, obj*);
obj* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1;
namespace lean {
obj* string_length(obj*);
}
namespace lean {
obj* mk_adhoc_ext_entry_core(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_inline_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
namespace lean {
obj* mk_std_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
obj* _init_l_Lean_ExternAttrData_inhabited() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
namespace lean {
obj* mk_extern_attr_data_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
}
obj* _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("identifier expected");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("string literal expected");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("adhoc");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("inline");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("string or identifier expected");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_stxInh;
x_7 = lean::array_get(x_6, x_1, x_2);
if (lean::obj_tag(x_7) == 3)
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = lean::cnstr_get(x_7, 2);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_2);
x_11 = lean::nat_dec_eq(x_10, x_4);
lean::dec(x_4);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::array_get(x_6, x_1, x_10);
x_13 = l_Lean_Syntax_isIdOrAtom___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Syntax_isStrLit___main(x_12);
lean::dec(x_12);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_3);
x_15 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2;
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::nat_add(x_10, x_9);
lean::dec(x_10);
x_18 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
obj* x_21; obj* x_22; uint8 x_23; 
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_22 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3;
x_23 = lean::string_dec_eq(x_21, x_22);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4;
x_25 = lean::string_dec_eq(x_21, x_24);
lean::dec(x_21);
if (x_25 == 0)
{
obj* x_26; 
x_26 = l_Lean_Syntax_isStrLit___main(x_12);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_3);
x_27 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
lean::dec(x_26);
x_29 = lean::nat_add(x_10, x_9);
lean::dec(x_10);
x_30 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
x_2 = x_29;
x_3 = x_31;
goto _start;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_12);
x_33 = lean::nat_add(x_10, x_9);
lean::dec(x_10);
x_34 = lean::array_get(x_6, x_1, x_33);
x_35 = l_Lean_Syntax_isStrLit___main(x_34);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; 
lean::dec(x_33);
lean::dec(x_8);
lean::dec(x_3);
x_36 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2;
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_38 = lean::nat_add(x_33, x_9);
lean::dec(x_33);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_8);
lean::cnstr_set(x_39, 1, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_3);
x_2 = x_38;
x_3 = x_40;
goto _start;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_21);
lean::dec(x_12);
x_42 = lean::nat_add(x_10, x_9);
lean::dec(x_10);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_8);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_3);
x_2 = x_42;
x_3 = x_44;
goto _start;
}
}
}
else
{
obj* x_46; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_3);
x_46 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5;
return x_46;
}
}
else
{
obj* x_47; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_47 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1;
return x_47;
}
}
else
{
obj* x_48; 
lean::dec(x_4);
lean::dec(x_2);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_3);
return x_48;
}
}
}
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_string("all");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
obj* _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("invalid extern attribute");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("all");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("unexpected kind of argument");
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_stxInh;
x_8 = lean::array_get(x_7, x_3, x_5);
x_9 = l_Lean_Syntax_isNatLit___main(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = l_Lean_Syntax_isStrLit___main(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_4);
x_11 = lean::box(0);
x_12 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(x_3, x_5, x_11);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_12);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_12, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_12, 0, x_18);
return x_12;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
lean::dec(x_12);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = lean::cnstr_get(x_10, 0);
lean::inc(x_22);
lean::dec(x_10);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_dec_eq(x_4, x_23);
lean::dec(x_4);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
x_25 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2;
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3;
x_27 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_22);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_9);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_8);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::array_get(x_7, x_3, x_32);
x_34 = l_Lean_Syntax_isStrLit___main(x_33);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; 
lean::dec(x_4);
x_35 = lean::box(0);
x_36 = l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main(x_3, x_32, x_35);
if (lean::obj_tag(x_36) == 0)
{
uint8 x_37; 
lean::dec(x_9);
x_37 = !lean::is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
lean::dec(x_36);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_36);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_36, 0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set(x_36, 0, x_42);
return x_36;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
lean::dec(x_36);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_9);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
obj* x_46; obj* x_47; uint8 x_48; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
lean::dec(x_34);
x_47 = lean::mk_nat_obj(2u);
x_48 = lean::nat_dec_eq(x_4, x_47);
lean::dec(x_4);
if (x_48 == 0)
{
obj* x_49; 
lean::dec(x_46);
lean::dec(x_9);
x_49 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2;
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_50 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3;
x_51 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_46);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_9);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
obj* x_56; 
lean::dec(x_4);
x_56 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4;
return x_56;
}
}
default: 
{
obj* x_57; 
x_57 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4;
return x_57;
}
}
}
}
obj* l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_addExtern___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_add_extern(x_1, x_2);
return x_3;
}
}
obj* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_2, 3);
x_7 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_1, x_3);
lean::inc(x_5);
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
x_9 = lean::array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
obj* _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Inhabited;
x_2 = l_Lean_ExternAttrData_inhabited;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_5);
x_7 = lean::array_swap(x_3, x_4, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_10 = lean::array_get(x_9, x_3, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::array_swap(x_3, x_4, x_5);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_20 = lean::nat_add(x_5, x_18);
lean::dec(x_5);
x_3 = x_17;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
}
obj* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_5 = lean::nat_add(x_2, x_3);
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
x_57 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_58 = lean::array_get(x_57, x_1, x_7);
x_59 = lean::array_get(x_57, x_1, x_2);
x_60 = lean::cnstr_get(x_58, 0);
lean::inc(x_60);
lean::dec(x_58);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_62 = l_Lean_Name_quickLt(x_60, x_61);
lean::dec(x_61);
lean::dec(x_60);
if (x_62 == 0)
{
x_8 = x_1;
goto block_56;
}
else
{
obj* x_63; 
x_63 = lean::array_swap(x_1, x_2, x_7);
x_8 = x_63;
goto block_56;
}
block_56:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_10 = lean::array_get(x_9, x_8, x_3);
x_11 = lean::array_get(x_9, x_8, x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::array_get(x_9, x_8, x_7);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_Lean_Name_quickLt(x_16, x_12);
lean::dec(x_12);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_18 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_10, x_8, x_2, x_2);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
x_21 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_20, x_2, x_19);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_19);
x_1 = x_21;
x_2 = x_23;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
x_25 = lean::array_swap(x_8, x_7, x_3);
lean::dec(x_7);
x_26 = lean::array_get(x_9, x_25, x_3);
lean::inc(x_2, 2);
x_27 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_26, x_25, x_2, x_2);
lean::dec(x_26);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_29, x_2, x_28);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_28, x_31);
lean::dec(x_28);
x_1 = x_30;
x_2 = x_32;
goto _start;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
lean::dec(x_12);
lean::dec(x_10);
x_34 = lean::array_swap(x_8, x_2, x_3);
x_35 = lean::array_get(x_9, x_34, x_7);
x_36 = lean::array_get(x_9, x_34, x_3);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_39 = l_Lean_Name_quickLt(x_37, x_38);
lean::dec(x_38);
lean::dec(x_37);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_40 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_36, x_34, x_2, x_2);
lean::dec(x_36);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_42, x_2, x_41);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_add(x_41, x_44);
lean::dec(x_41);
x_1 = x_43;
x_2 = x_45;
goto _start;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_36);
x_47 = lean::array_swap(x_34, x_7, x_3);
lean::dec(x_7);
x_48 = lean::array_get(x_9, x_47, x_3);
lean::inc(x_2, 2);
x_49 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_48, x_47, x_2, x_2);
lean::dec(x_48);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
lean::dec(x_49);
x_52 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_51, x_2, x_50);
x_53 = lean::mk_nat_obj(1u);
x_54 = lean::nat_add(x_50, x_53);
lean::dec(x_50);
x_1 = x_52;
x_2 = x_54;
goto _start;
}
}
}
}
}
}
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_2, x_1);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_4, x_5);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_3, x_7, x_6);
lean::dec(x_6);
return x_8;
}
}
obj* _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProjectionFnInfoExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProjectionFnInfoExtension___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1;
x_6 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2;
x_7 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3;
x_8 = l_Lean_registerParametricAttribute___rarg___closed__2;
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set(x_9, 4, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = lean::box(0);
lean::cnstr_set(x_10, 0, x_13);
lean::inc(x_12);
lean::inc(x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerParametricAttribute___rarg___lambda__4___boxed), 8, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_3);
lean::closure_set(x_14, 2, x_12);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_15, 0, x_1);
lean::inc(x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = l_Lean_registerTagAttribute___closed__5;
x_18 = l_Lean_registerTagAttribute___closed__6;
x_19 = 0;
x_20 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set(x_20, 2, x_14);
lean::cnstr_set(x_20, 3, x_15);
lean::cnstr_set(x_20, 4, x_16);
lean::cnstr_set(x_20, 5, x_17);
lean::cnstr_set(x_20, 6, x_18);
lean::cnstr_set(x_20, 7, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*8, x_19);
lean::inc(x_20);
x_21 = l_Lean_registerAttribute(x_20, x_10);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::dec(x_23);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_12);
lean::cnstr_set(x_21, 0, x_24);
return x_21;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_21, 1);
lean::inc(x_25);
lean::dec(x_21);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_12);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8 x_28; 
lean::dec(x_20);
lean::dec(x_12);
x_28 = !lean::is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_21, 0);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_21);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; 
x_32 = lean::cnstr_get(x_10, 0);
x_33 = lean::cnstr_get(x_10, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_10);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
lean::inc(x_32);
lean::inc(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerParametricAttribute___rarg___lambda__4___boxed), 8, 3);
lean::closure_set(x_36, 0, x_1);
lean::closure_set(x_36, 1, x_3);
lean::closure_set(x_36, 2, x_32);
lean::inc(x_1);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_37, 0, x_1);
lean::inc(x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_38, 0, x_1);
x_39 = l_Lean_registerTagAttribute___closed__5;
x_40 = l_Lean_registerTagAttribute___closed__6;
x_41 = 0;
x_42 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_42, 0, x_1);
lean::cnstr_set(x_42, 1, x_2);
lean::cnstr_set(x_42, 2, x_36);
lean::cnstr_set(x_42, 3, x_37);
lean::cnstr_set(x_42, 4, x_38);
lean::cnstr_set(x_42, 5, x_39);
lean::cnstr_set(x_42, 6, x_40);
lean::cnstr_set(x_42, 7, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*8, x_41);
lean::inc(x_42);
x_43 = l_Lean_registerAttribute(x_42, x_35);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_45 = x_43;
} else {
 lean::dec_ref(x_43);
 x_45 = lean::box(0);
}
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set(x_46, 1, x_32);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_42);
lean::dec(x_32);
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_43, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_50 = x_43;
} else {
 lean::dec_ref(x_43);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8 x_52; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_52 = !lean::is_exclusive(x_10);
if (x_52 == 0)
{
return x_10;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_10, 0);
x_54 = lean::cnstr_get(x_10, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_10);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
}
obj* l_Lean_mkExternAttr___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_2);
x_10 = l_Lean_Environment_isProjectionFn(x_1, x_2);
if (x_10 == 0)
{
uint8 x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_Lean_Environment_isConstructor(x_1, x_2);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_4, 0, x_12);
return x_4;
}
else
{
obj* x_13; 
lean::free_heap_obj(x_4);
x_13 = lean_add_extern(x_1, x_2);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
lean::dec(x_9);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_13);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_13, 0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_13, 0, x_19);
return x_13;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
}
}
else
{
obj* x_23; 
lean::free_heap_obj(x_4);
x_23 = lean_add_extern(x_1, x_2);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
lean::dec(x_9);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
lean::dec(x_23);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_23);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_23, 0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_23, 0, x_29);
return x_23;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
obj* x_33; uint8 x_34; 
x_33 = lean::cnstr_get(x_4, 0);
lean::inc(x_33);
lean::dec(x_4);
lean::inc(x_2);
x_34 = l_Lean_Environment_isProjectionFn(x_1, x_2);
if (x_34 == 0)
{
uint8 x_35; 
lean::inc(x_2);
lean::inc(x_1);
x_35 = l_Lean_Environment_isConstructor(x_1, x_2);
if (x_35 == 0)
{
obj* x_36; obj* x_37; 
lean::dec(x_2);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_1);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean_add_extern(x_1, x_2);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_33);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_40 = x_38;
} else {
 lean::dec_ref(x_38);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_39);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_43 = x_38;
} else {
 lean::dec_ref(x_38);
 x_43 = lean::box(0);
}
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_33);
lean::cnstr_set(x_44, 1, x_42);
if (lean::is_scalar(x_43)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_43;
}
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
obj* x_46; 
x_46 = lean_add_extern(x_1, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_33);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_50 = lean::cnstr_get(x_46, 0);
lean::inc(x_50);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_51 = x_46;
} else {
 lean::dec_ref(x_46);
 x_51 = lean::box(0);
}
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_33);
lean::cnstr_set(x_52, 1, x_50);
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
}
obj* _init_l_Lean_mkExternAttr___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("extern");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkExternAttr___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtin and foreign functions");
return x_1;
}
}
obj* _init_l_Lean_mkExternAttr___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkExternAttr___lambda__1___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_mkExternAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkExternAttr___closed__1;
x_3 = l_Lean_mkExternAttr___closed__2;
x_4 = l_Lean_mkExternAttr___closed__3;
x_5 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_mkExternAttr___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_mkExternAttr___lambda__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::nat_add(x_3, x_4);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
x_10 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_11 = lean::array_get(x_10, x_1, x_9);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8 x_15; 
lean::dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean::dec(x_12);
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_9, x_19);
lean::dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_3);
x_22 = lean::box(0);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_3);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_9, x_23);
lean::dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
obj* _init_l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_6, x_3);
lean::dec(x_3);
lean::dec(x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean::dec(x_8);
x_11 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::array_get_size(x_10);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_13, x_14);
lean::dec(x_13);
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_10, x_12, x_16, x_15);
lean::dec(x_12);
lean::dec(x_10);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
x_18 = lean::box(0);
return x_18;
}
else
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_17);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_17, 0);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
namespace lean {
obj* get_extern_attr_data_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_externattr_3__parseOptNum___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_Iterator_hasNext___main(x_2);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = 48;
x_12 = x_11 <= x_10;
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 57;
x_15 = x_10 <= x_14;
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_7);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = l_String_Iterator_next___main(x_2);
x_18 = lean::mk_nat_obj(10u);
x_19 = lean::nat_mul(x_3, x_18);
lean::dec(x_3);
x_20 = lean::uint32_to_nat(x_10);
x_21 = lean::mk_nat_obj(48u);
x_22 = lean::nat_sub(x_20, x_21);
lean::dec(x_20);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_22);
lean::dec(x_19);
x_1 = x_7;
x_2 = x_17;
x_3 = x_23;
goto _start;
}
}
}
}
else
{
obj* x_25; 
lean::dec(x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_3);
return x_25;
}
}
}
obj* l___private_init_lean_compiler_externattr_3__parseOptNum(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_externattr_3__parseOptNum___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_expandExternPatternAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = l_String_Iterator_hasNext___main(x_3);
if (x_9 == 0)
{
lean::dec(x_8);
lean::dec(x_3);
return x_4;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = 35;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_String_Iterator_next___main(x_3);
x_14 = lean::string_push(x_4, x_10);
x_2 = x_8;
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = l_String_Iterator_next___main(x_3);
x_17 = l_String_Iterator_remainingBytes___main(x_16);
x_18 = l___private_init_lean_compiler_externattr_3__parseOptNum___main(x_17, x_16, x_5);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
x_21 = lean::nat_sub(x_20, x_7);
lean::dec(x_20);
x_22 = l_List_getOpt___main___rarg(x_21, x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
x_23 = l_String_splitAux___main___closed__1;
x_24 = lean::string_append(x_4, x_23);
x_2 = x_8;
x_3 = x_19;
x_4 = x_24;
goto _start;
}
else
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_27 = lean::string_append(x_4, x_26);
lean::dec(x_26);
x_2 = x_8;
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Lean_expandExternPatternAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_expandExternPatternAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_expandExternPatternAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
namespace lean {
obj* expand_extern_pattern_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::string_length(x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_Lean_expandExternPatternAux___main(x_2, x_3, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* l_Lean_mkSimpleFnCall(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = l_Prod_HasRepr___rarg___closed__1;
x_4 = lean::string_append(x_1, x_3);
x_5 = l_List_reprAux___main___rarg___closed__1;
x_6 = l_List_intersperse___main___rarg(x_5, x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_7, x_6);
lean::dec(x_6);
x_9 = lean::string_append(x_4, x_8);
lean::dec(x_8);
x_10 = l_Option_HasRepr___rarg___closed__3;
x_11 = lean::string_append(x_9, x_10);
return x_11;
}
}
obj* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_expandExternEntry___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::expand_extern_pattern_core(x_4, x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
default: 
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = l_Lean_mkSimpleFnCall(x_7, x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_Lean_expandExternEntry(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_expandExternEntry___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_ExternEntry_backend___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend___main(x_1);
return x_2;
}
}
obj* l_Lean_ExternEntry_backend___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_getExternEntryForAux___main(obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_ExternEntry_backend___main(x_4);
x_7 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3;
x_8 = lean_name_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean_name_dec_eq(x_6, x_1);
lean::dec(x_6);
if (x_9 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
obj* x_11; 
lean::inc(x_4);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_4);
return x_11;
}
}
else
{
obj* x_12; 
lean::dec(x_6);
lean::inc(x_4);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_4);
return x_12;
}
}
}
}
obj* l_Lean_getExternEntryForAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getExternEntryForAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_getExternEntryForAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
namespace lean {
obj* get_extern_entry_for_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_getExternEntryForAux___main(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
namespace lean {
obj* mk_extern_call_core(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::get_extern_entry_for_core(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_expandExternEntry___main(x_6, x_3);
return x_7;
}
}
}
}
obj* l_Lean_getExternAttrDataOld___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
return x_3;
}
}
uint8 l_Lean_isExtern(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_3);
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_isExtern___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_isExternC(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_get_extern_attr_data(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 2)
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_11 = l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3;
x_12 = lean_name_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_9);
x_13 = 0;
return x_13;
}
else
{
if (lean::obj_tag(x_9) == 0)
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8 x_15; 
lean::dec(x_9);
x_15 = 0;
return x_15;
}
}
}
else
{
uint8 x_16; 
lean::dec(x_8);
lean::dec(x_6);
x_16 = 0;
return x_16;
}
}
}
}
}
obj* l_Lean_isExternC___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_getExternNameFor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_get_extern_attr_data(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::get_extern_entry_for_core(x_6, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_7, 0);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; 
lean::free_heap_obj(x_7);
lean::dec(x_10);
x_11 = lean::box(0);
return x_11;
}
case 1:
{
obj* x_12; 
lean::free_heap_obj(x_7);
lean::dec(x_10);
x_12 = lean::box(0);
return x_12;
}
default: 
{
obj* x_13; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
lean::cnstr_set(x_7, 0, x_13);
return x_7;
}
}
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_15; 
lean::dec(x_14);
x_15 = lean::box(0);
return x_15;
}
case 1:
{
obj* x_16; 
lean::dec(x_14);
x_16 = lean::box(0);
return x_16;
}
default: 
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
}
}
obj* l_Lean_getExternNameFor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_lean_expr(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_projfns(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_externattr(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_projfns(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkAdhocExtEntry"), 1, lean::mk_adhoc_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkInlineExtEntry"), 2, lean::mk_inline_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkStdExtEntry"), 2, lean::mk_std_ext_entry_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkForeignExtEntry"), 2, lean::mk_foreign_ext_entry_core);
l_Lean_ExternAttrData_inhabited = _init_l_Lean_ExternAttrData_inhabited();
lean::mark_persistent(l_Lean_ExternAttrData_inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ExternAttrData"), "inhabited"), l_Lean_ExternAttrData_inhabited);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkExternAttrData"), 2, lean::mk_extern_attr_data_core);
l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1 = _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__1);
l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2 = _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__2);
l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3 = _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__3);
l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4 = _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__4);
l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5 = _init_l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_externattr_1__syntaxToExternEntries___main___closed__5);
l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1 = _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__1);
l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2 = _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__2);
l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3 = _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__3);
l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4 = _init_l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_externattr_2__syntaxToExternAttrData___closed__4);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "addExtern"), 2, l_Lean_addExtern___boxed);
l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1 = _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1();
lean::mark_persistent(l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1);
l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1 = _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1();
lean::mark_persistent(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1);
l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2 = _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2();
lean::mark_persistent(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__2);
l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3 = _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3();
lean::mark_persistent(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__3);
l_Lean_mkExternAttr___closed__1 = _init_l_Lean_mkExternAttr___closed__1();
lean::mark_persistent(l_Lean_mkExternAttr___closed__1);
l_Lean_mkExternAttr___closed__2 = _init_l_Lean_mkExternAttr___closed__2();
lean::mark_persistent(l_Lean_mkExternAttr___closed__2);
l_Lean_mkExternAttr___closed__3 = _init_l_Lean_mkExternAttr___closed__3();
lean::mark_persistent(l_Lean_mkExternAttr___closed__3);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkExternAttr"), 1, l_Lean_mkExternAttr);
w = l_Lean_mkExternAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_externAttr = io_result_get_value(w);
lean::mark_persistent(l_Lean_externAttr);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "externAttr"), l_Lean_externAttr);
l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1 = _init_l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1();
lean::mark_persistent(l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternAttrData"), 2, lean::get_extern_attr_data_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternPatternAux"), 4, l_Lean_expandExternPatternAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternPattern"), 2, lean::expand_extern_pattern_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkSimpleFnCall"), 2, l_Lean_mkSimpleFnCall);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "expandExternEntry"), 2, l_Lean_expandExternEntry);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ExternEntry"), "backend"), 1, l_Lean_ExternEntry_backend___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternEntryForAux"), 2, l_Lean_getExternEntryForAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternEntryFor"), 2, lean::get_extern_entry_for_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkExternCall"), 3, lean::mk_extern_call_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternAttrDataOld"), 2, l_Lean_getExternAttrDataOld___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isExtern"), 2, l_Lean_isExtern___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "isExternC"), 2, l_Lean_isExternC___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "getExternNameFor"), 3, l_Lean_getExternNameFor___boxed);
return w;
}
