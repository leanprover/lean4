// Lean compiler output
// Module: Init.Lean.Elab.Util
// Imports: Init.Lean.Util.Trace Init.Lean.Parser
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
lean_object* l_Lean_fmt___at_Lean_Elab_mkElabAttribute___spec__1(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* lean_get_namespaces(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute(lean_object*);
lean_object* l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__1;
lean_object* l_Lean_Elab_ElabAttribute_inhabited(lean_object*);
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_ElabAttribute_inhabited___rarg(lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
lean_object* _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Elab_checkSyntaxNodeKind___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Elab_checkSyntaxNodeKind___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_Lean_Elab_checkSyntaxNodeKind___closed__1;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Name_append___main(x_6, x_1);
x_9 = l_Lean_Elab_checkSyntaxNodeKind(x_8, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_7;
x_3 = x_10;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax node kind is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid syntax node kind '");
return x_1;
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_get_namespaces(x_1);
lean_inc(x_8);
x_10 = l_Lean_Name_append___main(x_2, x_8);
x_11 = l_Lean_Name_toString___closed__1;
lean_inc(x_8);
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_8);
x_13 = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean_string_append(x_14, x_15);
lean_inc(x_8);
x_17 = l_Lean_Elab_checkSyntaxNodeKind(x_8, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___main(x_8, x_9, x_18);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_16);
lean_dec(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_checkSyntaxNodeKind(x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_16);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_ElabAttribute_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_10 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_11 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_AttributeImpl_inhabited___closed__6;
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_ElabAttribute_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_ElabAttribute_inhabited___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_fmt___at_Lean_Elab_mkElabAttribute___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_ref_get(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" elaborator attribute");
return x_1;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1;
x_4 = lean_string_append(x_1, x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" elaborator");
return x_1;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_4);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_10 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_8);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_1, x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_3);
x_16 = lean_string_append(x_3, x_15);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = l_Lean_AttributeImpl_inhabited___closed__1;
x_20 = l_Lean_AttributeImpl_inhabited___closed__4;
x_21 = l_Lean_AttributeImpl_inhabited___closed__5;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*8, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_3);
x_28 = lean_string_append(x_3, x_27);
lean_inc(x_2);
x_29 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_29, 0, x_2);
lean_inc(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_30, 0, x_2);
x_31 = l_Lean_AttributeImpl_inhabited___closed__1;
x_32 = l_Lean_AttributeImpl_inhabited___closed__4;
x_33 = l_Lean_AttributeImpl_inhabited___closed__5;
x_34 = 0;
x_35 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_35, 7, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*8, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Elab_mkElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_mkElabAttribute___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_mkElabAttribute___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init_Lean_Util_Trace(lean_object*);
lean_object* initialize_Init_Lean_Parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Parser(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_checkSyntaxNodeKind___closed__1 = _init_l_Lean_Elab_checkSyntaxNodeKind___closed__1();
lean_mark_persistent(l_Lean_Elab_checkSyntaxNodeKind___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2();
lean_mark_persistent(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2);
l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___closed__1);
l_Lean_Elab_mkElabAttribute___rarg___closed__1 = _init_l_Lean_Elab_mkElabAttribute___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___rarg___closed__1);
l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1);
l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2 = _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2);
l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3 = _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__3);
l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4 = _init_l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4);
res = l___private_Init_Lean_Elab_Util_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
