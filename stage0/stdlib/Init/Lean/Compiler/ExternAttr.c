// Lean compiler output
// Module: Init.Lean.Compiler.ExternAttr
// Imports: Init.Data.Option.Basic Init.Lean.Expr Init.Lean.Environment Init.Lean.Attributes Init.Lean.ProjFns
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_string_push(lean_object*, uint32_t);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* l_Lean_Syntax_isIdOrAtom___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_getExternEntryForAux(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr(lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6;
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed(lean_object*);
lean_object* l_Lean_getExternNameFor___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__4___closed__1;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_mkProjectionFnInfoExtension___closed__3;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_ExternAttrData_inhabited___closed__1;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_registerTagAttribute___closed__1;
lean_object* l_Lean_expandExternPattern(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_intersperse___main___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ExternEntry_backend___boxed(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2;
lean_object* l_Lean_getExternNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_Lean_expandExternPattern___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
lean_object* l_Lean_ExternEntry_backend(lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExternC(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
lean_object* l_Lean_ExternAttrData_inhabited;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* lean_add_extern(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___boxed(lean_object*);
lean_object* l_Lean_expandExternPatternAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_mkExternAttr___closed__1;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6;
lean_object* l_Lean_isExtern___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__2;
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_mkExternAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3;
lean_object* l_Lean_Environment_getModuleIdxFor(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_isExternC___boxed(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(lean_object*);
lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__3;
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_mkExternAttr___closed__5;
lean_object* l_Lean_addExtern___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryFor(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_expandExternPatternAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryForAux___boxed(lean_object*, lean_object*);
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExternAttr___closed__4;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7;
lean_object* l_Lean_getExternEntryForAux___main___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_remainingBytes(lean_object*);
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__1;
lean_object* l_Lean_getExternEntryForAux___main(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleFnCall(lean_object*, lean_object*);
lean_object* l_Lean_getExternEntryFor___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5;
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8;
lean_object* l_Lean_externAttr;
lean_object* l_Lean_mkExternAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8;
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(lean_object*);
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit___rarg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_ExternAttrData_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ExternAttrData_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExternAttrData_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string literal expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("adhoc");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inline");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string or identifier expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_eq(x_2, x_4);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_array_get(x_8, x_1, x_2);
if (lean_obj_tag(x_9) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_13 = lean_nat_dec_eq(x_12, x_4);
lean_dec(x_4);
x_14 = l_Bool_DecidableEq(x_13, x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_get(x_8, x_1, x_12);
x_16 = l_Lean_Syntax_isIdOrAtom___rarg(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Syntax_isStrLit___rarg(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_18 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
x_2 = x_20;
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5;
x_26 = lean_string_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6;
x_28 = lean_string_dec_eq(x_24, x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Syntax_isStrLit___rarg(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_30 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_32;
x_3 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_15);
x_36 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_37 = lean_array_get(x_8, x_1, x_36);
x_38 = l_Lean_Syntax_isStrLit___rarg(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_10);
lean_dec(x_3);
x_39 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4;
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_nat_add(x_36, x_11);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
x_2 = x_41;
x_3 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_24);
lean_dec(x_15);
x_45 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
x_2 = x_45;
x_3 = x_47;
goto _start;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_49 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8;
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2;
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_4);
lean_dec(x_2);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_3);
return x_51;
}
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("all");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid extern attribute");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of argument");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = lean_array_get(x_39, x_3, x_5);
x_41 = l_Lean_numLitKind;
x_42 = l_Lean_Syntax_isNatLitAux___rarg(x_41, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
x_9 = x_43;
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_9 = x_45;
goto block_38;
}
block_38:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_get(x_12, x_3, x_11);
x_14 = l_Lean_Syntax_isStrLit___rarg(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main(x_3, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_nat_dec_eq(x_4, x_28);
lean_dec(x_28);
lean_dec(x_4);
x_30 = l_Bool_DecidableEq(x_29, x_7);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_10);
x_31 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8;
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_4);
x_46 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
return x_46;
}
}
default: 
{
lean_object* x_47; 
x_47 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10;
return x_47;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_addExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_extern(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_inhabited;
x_2 = l_Lean_ExternAttrData_inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_9 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean_dec(x_11);
x_14 = 1;
x_15 = l_Bool_DecidableEq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_swap(x_3, x_4, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_22 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_3 = x_19;
x_4 = x_21;
x_5 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_46 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_47 = lean_array_get(x_46, x_1, x_16);
x_48 = lean_array_get(x_46, x_1, x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Name_quickLt(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
x_52 = 1;
x_53 = l_Bool_DecidableEq(x_51, x_52);
if (x_53 == 0)
{
x_17 = x_1;
goto block_45;
}
else
{
lean_object* x_54; 
x_54 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_54;
goto block_45;
}
block_45:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_18 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Name_quickLt(x_21, x_22);
lean_dec(x_22);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = lean_array_get(x_18, x_17, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Name_quickLt(x_27, x_21);
lean_dec(x_21);
lean_dec(x_27);
x_29 = l_Bool_DecidableEq(x_28, x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_30;
goto block_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_31 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_32 = lean_array_get(x_18, x_31, x_3);
lean_inc_n(x_2, 2);
x_33 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_32, x_31, x_2, x_2);
lean_dec(x_32);
x_4 = x_33;
goto block_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; 
lean_dec(x_21);
lean_dec(x_19);
x_34 = lean_array_swap(x_17, x_2, x_3);
x_35 = lean_array_get(x_18, x_34, x_16);
x_36 = lean_array_get(x_18, x_34, x_3);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = l_Lean_Name_quickLt(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_40 = l_Bool_DecidableEq(x_39, x_24);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_41 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_36, x_34, x_2, x_2);
lean_dec(x_36);
x_4 = x_41;
goto block_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
x_42 = lean_array_swap(x_34, x_16, x_3);
lean_dec(x_16);
x_43 = lean_array_get(x_18, x_42, x_3);
lean_inc_n(x_2, 2);
x_44 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_3, x_43, x_42, x_2, x_2);
lean_dec(x_43);
x_4 = x_44;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = 1;
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Bool_DecidableEq(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_3);
x_11 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_12 = lean_io_ref_get(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
lean_dec(x_13);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__4___closed__1;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_io_ref_get(x_11, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_ref_reset(x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_17);
x_24 = x_17;
x_25 = lean_array_push(x_19, x_24);
x_26 = lean_io_ref_set(x_11, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_17);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_17);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_49 = 1;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
x_51 = l_Bool_DecidableEq(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_55 = lean_io_ref_get(x_54, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_get_size(x_56);
lean_dec(x_56);
x_59 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__4___closed__1;
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_io_ref_get(x_54, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_io_ref_reset(x_54, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_60);
x_67 = x_60;
x_68 = lean_array_push(x_62, x_67);
x_69 = lean_io_ref_set(x_54, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_60);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_60);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_85 = lean_ctor_get(x_55, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_87 = x_55;
} else {
 lean_dec_ref(x_55);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
return x_3;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_3, 0);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_3);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_Array_empty___closed__1;
lean_inc(x_13);
x_15 = lean_apply_1(x_13, x_14);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__7(x_17, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_io_ref_get(x_3, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_io_ref_reset(x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_25);
x_32 = x_25;
x_33 = lean_array_push(x_27, x_32);
x_34 = lean_io_ref_set(x_3, x_33, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_25);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
return x_29;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_29, 0);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_29);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_25);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_13);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_System_FilePath_dirName___closed__1;
x_57 = l_Lean_Name_toStringWithSep___main(x_56, x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_61 = lean_string_append(x_59, x_60);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_61);
return x_4;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_64 = lean_array_get_size(x_62);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6(x_1, x_62, x_62, x_64, x_65);
lean_dec(x_64);
lean_dec(x_62);
x_67 = 1;
x_68 = l_Bool_DecidableEq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = l_Array_empty___closed__1;
lean_inc(x_69);
x_71 = lean_apply_1(x_69, x_70);
x_72 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_73 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_73, 0, x_71);
lean_closure_set(x_73, 1, x_72);
x_74 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__7(x_73, x_63);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 4);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_io_ref_get(x_3, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_io_ref_reset(x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_81);
x_88 = x_81;
x_89 = lean_array_push(x_83, x_88);
x_90 = lean_io_ref_set(x_3, x_89, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_81);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_83);
lean_dec(x_81);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_100 = x_85;
} else {
 lean_dec_ref(x_85);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_81);
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_104 = x_82;
} else {
 lean_dec_ref(x_82);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_69);
lean_dec(x_1);
x_106 = lean_ctor_get(x_74, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_108 = x_74;
} else {
 lean_dec_ref(x_74);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
lean_dec(x_1);
x_111 = l_System_FilePath_dirName___closed__1;
x_112 = l_Lean_Name_toStringWithSep___main(x_111, x_110);
x_113 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_63);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_2, x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_3, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_registerTagAttribute___closed__1;
x_7 = l_Lean_mkProjectionFnInfoExtension___closed__3;
x_8 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1;
x_9 = l_Lean_registerParametricAttribute___rarg___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_9);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkExternAttr___spec__5(x_10, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___rarg___lambda__4___boxed), 9, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_4);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__4;
x_18 = l_Lean_AttributeImpl_inhabited___closed__5;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_17);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*8, x_19);
lean_inc(x_20);
x_21 = l_Lean_registerAttribute(x_20, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_12);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_mkExternAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData(x_3);
return x_4;
}
}
lean_object* l_Lean_mkExternAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_2);
x_4 = l_Lean_Environment_isProjectionFn(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_Environment_isConstructor(x_1, x_2);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_add_extern(x_1, x_2);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = l_String_Iterator_extract___closed__1;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_add_extern(x_1, x_2);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extern");
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkExternAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtin and foreign functions");
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkExternAttr___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_mkExternAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkExternAttr___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_mkExternAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_mkExternAttr___closed__2;
x_3 = l_Lean_mkExternAttr___closed__3;
x_4 = l_Lean_mkExternAttr___closed__4;
x_5 = l_Lean_mkExternAttr___closed__5;
x_6 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_mkExternAttr___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_mkExternAttr___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_mkExternAttr___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_mkExternAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkExternAttr___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_mkExternAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkExternAttr___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = l_Lean_Name_quickLt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
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
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
lean_dec(x_4);
x_17 = l_Lean_Name_quickLt(x_13, x_12);
lean_dec(x_12);
x_18 = l_Bool_DecidableEq(x_17, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_11);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; 
lean_dec(x_11);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_9, x_20);
x_22 = l_Bool_DecidableEq(x_21, x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_9, x_23);
lean_dec(x_9);
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_3);
x_26 = lean_box(0);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
x_3 = x_28;
goto _start;
}
}
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean_dec(x_8);
x_11 = l_Lean_ExternAttrData_inhabited___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_10, x_12, x_16, x_15);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
lean_object* lean_get_extern_attr_data(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_RBNode_find___main___at_Lean_getExternAttrData___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_getExternAttrData___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_getExternAttrData___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_38; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_38 = l_String_Iterator_hasNext(x_2);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 1;
x_8 = x_39;
goto block_37;
}
else
{
uint8_t x_40; 
x_40 = 0;
x_8 = x_40;
goto block_37;
}
block_37:
{
uint8_t x_9; uint8_t x_10; 
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = l_String_Iterator_curr(x_2);
x_12 = 48;
x_13 = x_12 <= x_11;
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_String_Iterator_next(x_2);
x_17 = lean_unsigned_to_nat(10u);
x_18 = lean_nat_mul(x_3, x_17);
lean_dec(x_3);
x_19 = lean_uint32_to_nat(x_11);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_nat_add(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_1 = x_7;
x_2 = x_16;
x_3 = x_22;
goto _start;
}
}
else
{
uint32_t x_24; uint8_t x_25; uint8_t x_26; 
x_24 = 57;
x_25 = x_11 <= x_24;
x_26 = l_Bool_DecidableEq(x_25, x_9);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_String_Iterator_next(x_2);
x_29 = lean_unsigned_to_nat(10u);
x_30 = lean_nat_mul(x_3, x_29);
lean_dec(x_3);
x_31 = lean_uint32_to_nat(x_11);
x_32 = lean_unsigned_to_nat(48u);
x_33 = lean_nat_sub(x_31, x_32);
lean_dec(x_31);
x_34 = lean_nat_add(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_1 = x_7;
x_2 = x_28;
x_3 = x_34;
goto _start;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
}
lean_object* l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_expandExternPatternAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = l_String_Iterator_hasNext(x_3);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
else
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_12 = l_String_Iterator_curr(x_3);
x_13 = 35;
x_14 = l_Char_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_String_Iterator_next(x_3);
x_16 = lean_string_push(x_4, x_12);
x_2 = x_8;
x_3 = x_15;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = l_String_Iterator_next(x_3);
x_19 = l_String_Iterator_remainingBytes(x_18);
x_20 = l___private_Init_Lean_Compiler_ExternAttr_3__parseOptNum___main(x_19, x_18, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_sub(x_22, x_7);
lean_dec(x_22);
x_24 = l_String_splitAux___main___closed__1;
x_25 = l_List_getD___rarg(x_23, x_1, x_24);
x_26 = lean_string_append(x_4, x_25);
lean_dec(x_25);
x_2 = x_8;
x_3 = x_21;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l_Lean_expandExternPatternAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_expandExternPatternAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_expandExternPatternAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandExternPatternAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_expandExternPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_string_length(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_Lean_expandExternPatternAux___main(x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_expandExternPattern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_expandExternPattern(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_mkSimpleFnCall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Prod_HasRepr___rarg___closed__1;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_List_reprAux___main___rarg___closed__1;
x_6 = l_List_intersperse___main___rarg(x_5, x_2);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_7, x_6);
lean_dec(x_6);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = l_Option_HasRepr___rarg___closed__3;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
lean_object* l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkSimpleFnCall___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ExternEntry_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_ExternEntry_backend___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExternEntry_backend(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_getExternEntryForAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_ExternEntry_backend(x_4);
x_7 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2;
x_8 = lean_name_eq(x_6, x_7);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_14; 
lean_inc(x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_inc(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
}
lean_object* l_Lean_getExternEntryForAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getExternEntryForAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_getExternEntryForAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryForAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getExternEntryFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_getExternEntryForAux___main(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getExternEntryFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getExternEntryFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_isExtern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
lean_object* l_Lean_isExtern___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExtern(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isExternC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_externAttr;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_3, x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = 0;
return x_16;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
x_18 = 0;
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_19 = 0;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_7);
x_20 = 0;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_7);
x_21 = 0;
return x_21;
}
}
}
}
}
lean_object* l_Lean_isExternC___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isExternC(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_getExternNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_externAttr;
x_5 = l_Lean_ParametricAttribute_getParam___at_Lean_getExternAttrData___spec__1(x_4, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_getExternEntryFor(x_7, x_2);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
case 3:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
default: 
{
lean_object* x_14; 
lean_free_object(x_8);
lean_dec(x_11);
x_14 = lean_box(0);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
switch (lean_obj_tag(x_15)) {
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_box(0);
return x_20;
}
}
}
}
}
}
}
lean_object* l_Lean_getExternNameFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getExternNameFor(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Lean_Expr(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Attributes(lean_object*);
lean_object* initialize_Init_Lean_ProjFns(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_ExternAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ExternAttrData_inhabited___closed__1 = _init_l_Lean_ExternAttrData_inhabited___closed__1();
lean_mark_persistent(l_Lean_ExternAttrData_inhabited___closed__1);
l_Lean_ExternAttrData_inhabited = _init_l_Lean_ExternAttrData_inhabited();
lean_mark_persistent(l_Lean_ExternAttrData_inhabited);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__1);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__2);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__3);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__4);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__5);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__6);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__7);
l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8 = _init_l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_1__syntaxToExternEntries___main___closed__8);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__1);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__2);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__3);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__4);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__5);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__6);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__7);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__8);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__9);
l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10 = _init_l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10();
lean_mark_persistent(l___private_Init_Lean_Compiler_ExternAttr_2__syntaxToExternAttrData___closed__10);
l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1 = _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_mkExternAttr___spec__4___closed__1);
l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1 = _init_l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1();
lean_mark_persistent(l_Lean_registerParametricAttribute___at_Lean_mkExternAttr___spec__1___closed__1);
l_Lean_mkExternAttr___closed__1 = _init_l_Lean_mkExternAttr___closed__1();
lean_mark_persistent(l_Lean_mkExternAttr___closed__1);
l_Lean_mkExternAttr___closed__2 = _init_l_Lean_mkExternAttr___closed__2();
lean_mark_persistent(l_Lean_mkExternAttr___closed__2);
l_Lean_mkExternAttr___closed__3 = _init_l_Lean_mkExternAttr___closed__3();
lean_mark_persistent(l_Lean_mkExternAttr___closed__3);
l_Lean_mkExternAttr___closed__4 = _init_l_Lean_mkExternAttr___closed__4();
lean_mark_persistent(l_Lean_mkExternAttr___closed__4);
l_Lean_mkExternAttr___closed__5 = _init_l_Lean_mkExternAttr___closed__5();
lean_mark_persistent(l_Lean_mkExternAttr___closed__5);
res = l_Lean_mkExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_externAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_externAttr);
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
