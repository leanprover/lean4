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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_args___default;
lean_object* l_Lean_withRef___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedAttribute;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_instToFormatAttribute(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
extern lean_object* l_term_x5b___x2c_x5d___closed__11;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1135____closed__10;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Attribute_kind___default;
lean_object* l_Lean_Elab_instToFormatAttribute_match__1(lean_object*);
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_Elab_elabAttrs(lean_object*);
lean_object* l_Lean_Elab_elabAttr(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_38____closed__6;
lean_object* l_Lean_Elab_instInhabitedAttribute___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___closed__1;
lean_object* l_Lean_Elab_elabDeclAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr_match__1(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
extern lean_object* l_Lean_commandScopedLocalUnif__hint______Where___x7c_x2d_u22a2_____closed__5;
lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l_Lean_Elab_elabDeclAttrs(lean_object*);
extern lean_object* l_Lean_commandScopedLocalUnif__hint______Where___x7c_x2d_u22a2_____closed__3;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_instToFormatAttribute___closed__2;
lean_object* l_Lean_Elab_instToFormatAttribute___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__2;
lean_object* l_Lean_Elab_instToFormatAttribute___closed__3;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_instToFormatAttribute_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkAttrKindGlobal;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1135____closed__16;
lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
uint8_t l_Lean_Elab_toAttributeKind(lean_object*);
lean_object* l_Lean_Elab_instToFormatAttribute_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Elab_mkAttrKindGlobal___closed__4;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_Lean_Elab_Attribute_kind___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Attribute_args___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Elab_instToFormatAttribute_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_instToFormatAttribute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_instToFormatAttribute_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_instToFormatAttribute_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_instToFormatAttribute_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1135____closed__10;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instToFormatAttribute___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instToFormatAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1135____closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_instToFormatAttribute(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___spec__1(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Syntax_isMissing(x_5);
switch (x_2) {
case 0:
{
lean_object* x_42; 
x_42 = l_Lean_instInhabitedParserDescr___closed__1;
x_7 = x_42;
goto block_41;
}
case 1:
{
lean_object* x_43; 
x_43 = l_Lean_commandScopedLocalUnif__hint______Where___x7c_x2d_u22a2_____closed__5;
x_7 = x_43;
goto block_41;
}
default: 
{
lean_object* x_44; 
x_44 = l_Lean_commandScopedLocalUnif__hint______Where___x7c_x2d_u22a2_____closed__3;
x_7 = x_44;
goto block_41;
}
}
block_41:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Format_join___closed__1;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
if (x_6 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_14 = lean_box(0);
x_15 = 0;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_formatStxAux(x_14, x_15, x_16, x_5);
x_18 = lean_box(0);
x_19 = l_Lean_Format_pretty(x_17, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Lean_Elab_instToFormatAttribute___closed__3;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Format_sbracket___closed__4;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_instToFormatAttribute___closed__2;
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = 0;
x_30 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_dec(x_5);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_9);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
x_33 = l_Lean_Elab_instToFormatAttribute___closed__3;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Format_sbracket___closed__4;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_instToFormatAttribute___closed__2;
x_38 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = 0;
x_40 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAttribute___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedAttribute() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedAttribute___closed__1;
return x_1;
}
}
uint8_t l_Lean_Elab_toAttributeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getKind(x_5);
x_7 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1135____closed__16;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = 0;
return x_11;
}
}
}
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_toAttributeKind(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkAttrKindGlobal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attrKind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkAttrKindGlobal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_38____closed__6;
x_2 = l_Lean_Elab_mkAttrKindGlobal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkAttrKindGlobal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkAttrKindGlobal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkAttrKindGlobal___closed__2;
x_2 = l_Lean_Elab_mkAttrKindGlobal___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkAttrKindGlobal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_mkAttrKindGlobal___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_elabAttr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabAttr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_2);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getNumArgs(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_8);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_box(0);
x_24 = lean_box(x_3);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_4);
lean_closure_set(x_25, 3, x_23);
x_26 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_22, x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute [");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x2c_x5d___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_isAttribute(x_9, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___rarg(x_2, x_6, x_7, x_8, lean_box(0), x_17);
x_19 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
x_24 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_23, x_11);
return x_24;
}
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(x_4);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__3___boxed), 9, 8);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_9);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_7);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = l_Lean_Elab_toAttributeKind(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
x_12 = lean_box(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__4___boxed), 8, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_5);
x_14 = l_Lean_Syntax_isIdOrAtom_x3f(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = l_Lean_Elab_elabAttr___rarg___closed__3;
lean_inc(x_4);
x_17 = l_Lean_throwError___rarg(x_1, x_3, x_4, x_5, lean_box(0), x_16);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_withRef___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_17);
lean_inc(x_15);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_20, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_name_mk_string(x_26, x_22);
x_28 = lean_apply_2(x_25, lean_box(0), x_27);
x_29 = lean_apply_4(x_23, lean_box(0), lean_box(0), x_28, x_13);
return x_29;
}
}
}
lean_object* l_Lean_Elab_elabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_elabAttr___rarg___lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_elabAttr___rarg___lambda__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_elabAttr___rarg___lambda__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Elab_elabAttr___rarg___lambda__4(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_push(x_1, x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_9 < x_8;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_elabAttr___rarg(x_1, x_2, x_3, x_4, x_5, x_15);
lean_inc(x_6);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_6);
lean_inc(x_6);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_box_usize(x_9);
x_21 = lean_box_usize(x_8);
x_22 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2___boxed), 10, 9);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_21);
x_23 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_19, x_22);
return x_23;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Syntax_getSepArgs(x_6);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_10, x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___rarg___lambda__1), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_elabAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabAttrs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = l_Lean_Elab_elabAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeclAttrs___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabDeclAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_MonadEnv(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Attributes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Elab_Attribute_kind___default = _init_l_Lean_Elab_Attribute_kind___default();
l_Lean_Elab_Attribute_args___default = _init_l_Lean_Elab_Attribute_args___default();
lean_mark_persistent(l_Lean_Elab_Attribute_args___default);
l_Lean_Elab_instToFormatAttribute___closed__1 = _init_l_Lean_Elab_instToFormatAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_instToFormatAttribute___closed__1);
l_Lean_Elab_instToFormatAttribute___closed__2 = _init_l_Lean_Elab_instToFormatAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_instToFormatAttribute___closed__2);
l_Lean_Elab_instToFormatAttribute___closed__3 = _init_l_Lean_Elab_instToFormatAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_instToFormatAttribute___closed__3);
l_Lean_Elab_instInhabitedAttribute___closed__1 = _init_l_Lean_Elab_instInhabitedAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedAttribute___closed__1);
l_Lean_Elab_instInhabitedAttribute = _init_l_Lean_Elab_instInhabitedAttribute();
lean_mark_persistent(l_Lean_Elab_instInhabitedAttribute);
l_Lean_Elab_mkAttrKindGlobal___closed__1 = _init_l_Lean_Elab_mkAttrKindGlobal___closed__1();
lean_mark_persistent(l_Lean_Elab_mkAttrKindGlobal___closed__1);
l_Lean_Elab_mkAttrKindGlobal___closed__2 = _init_l_Lean_Elab_mkAttrKindGlobal___closed__2();
lean_mark_persistent(l_Lean_Elab_mkAttrKindGlobal___closed__2);
l_Lean_Elab_mkAttrKindGlobal___closed__3 = _init_l_Lean_Elab_mkAttrKindGlobal___closed__3();
lean_mark_persistent(l_Lean_Elab_mkAttrKindGlobal___closed__3);
l_Lean_Elab_mkAttrKindGlobal___closed__4 = _init_l_Lean_Elab_mkAttrKindGlobal___closed__4();
lean_mark_persistent(l_Lean_Elab_mkAttrKindGlobal___closed__4);
l_Lean_Elab_mkAttrKindGlobal = _init_l_Lean_Elab_mkAttrKindGlobal();
lean_mark_persistent(l_Lean_Elab_mkAttrKindGlobal);
l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__3___closed__1);
l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2);
l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3);
l_Lean_Elab_elabAttr___rarg___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__1);
l_Lean_Elab_elabAttr___rarg___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__2);
l_Lean_Elab_elabAttr___rarg___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
