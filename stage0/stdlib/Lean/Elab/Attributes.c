// Lean compiler output
// Module: Lean.Elab.Attributes
// Imports: Init Lean.Parser.Basic Lean.Attributes Lean.MonadEnv
#include <lean/lean.h>
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
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_inhabited;
lean_object* l_Lean_withRef___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributes___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_AttributeApplicationTime_beq(uint8_t, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__1;
lean_object* l_Lean_Elab_applyAttributes(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_Elab_applyAttributes___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_applyAttributesImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat(lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__2;
lean_object* l_Lean_Elab_elabAttr___rarg___closed__2;
lean_object* l_Lean_Elab_applyAttributesImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___closed__1;
extern lean_object* l_Lean_Format_sbracket___closed__3;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Attribute_inhabited___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__3;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@[");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Attribute_hasFormat___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Attribute_hasFormat___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Attribute_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_isMissing(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_formatStxAux___main(x_8, x_9, x_10, x_6);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
x_16 = l_Lean_Elab_Attribute_hasFormat___closed__3;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
x_18 = l_Lean_Format_sbracket___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_9);
x_20 = l_Lean_Elab_Attribute_hasFormat___closed__2;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_23 = 0;
x_24 = l_Lean_Format_join___closed__1;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_Elab_Attribute_hasFormat___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_sbracket___closed__3;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_23);
x_30 = l_Lean_Elab_Attribute_hasFormat___closed__2;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_format_group(x_31);
return x_32;
}
}
}
lean_object* _init_l_Lean_Elab_Attribute_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Attribute_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Attribute_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getNumArgs(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute [");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_isAttribute(x_6, x_1);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_1);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___rarg(x_3, x_4, lean_box(0), x_13);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_19, x_8);
return x_20;
}
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Syntax_isIdOrAtom_x3f(x_6);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__3), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Elab_elabAttr___rarg___closed__3;
lean_inc(x_3);
x_11 = l_Lean_throwError___rarg(x_1, x_3, lean_box(0), x_10);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_withRef___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
lean_inc(x_7);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_3);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_16);
x_21 = lean_apply_2(x_18, lean_box(0), x_20);
x_22 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_21, x_9);
return x_22;
}
}
}
lean_object* l_Lean_Elab_elabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttr___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabAttr___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_nat_add(x_1, x_2);
x_9 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(x_3, x_4, x_5, x_2, x_6, x_8, x_7);
return x_9;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Elab_elabAttr___rarg(x_1, x_2, x_3, x_13);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_7);
lean_inc(x_14);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_5);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(x_1, x_2, x_3, x_8, x_7, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_elabAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttrs___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = l_Lean_getAttributeImpl(x_16, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__6___rarg(x_21, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*3);
x_29 = l_Lean_AttributeApplicationTime_beq(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_12);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_4 = x_31;
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_27, 2);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = 1;
x_36 = lean_box(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_37 = lean_apply_6(x_33, x_1, x_34, x_36, x_5, x_6, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_4, x_39);
lean_dec(x_4);
x_4 = x_40;
x_7 = x_38;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_applyAttributesImp(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_1, x_3, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Array_forMAux___main___at_Lean_Elab_applyAttributesImp___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_applyAttributesImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_applyAttributesImp(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Elab_applyAttributes___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_applyAttributesImp___boxed), 6, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_applyAttributes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_applyAttributes___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_applyAttributes___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_applyAttributes___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_MonadEnv(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Attributes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Attribute_hasFormat___closed__1 = _init_l_Lean_Elab_Attribute_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__1);
l_Lean_Elab_Attribute_hasFormat___closed__2 = _init_l_Lean_Elab_Attribute_hasFormat___closed__2();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__2);
l_Lean_Elab_Attribute_hasFormat___closed__3 = _init_l_Lean_Elab_Attribute_hasFormat___closed__3();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__3);
l_Lean_Elab_Attribute_inhabited___closed__1 = _init_l_Lean_Elab_Attribute_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Attribute_inhabited___closed__1);
l_Lean_Elab_Attribute_inhabited = _init_l_Lean_Elab_Attribute_inhabited();
lean_mark_persistent(l_Lean_Elab_Attribute_inhabited);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3);
l_Lean_Elab_elabAttr___rarg___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__1);
l_Lean_Elab_elabAttr___rarg___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__2);
l_Lean_Elab_elabAttr___rarg___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
