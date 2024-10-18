// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Rename Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.TerminationArgument Lean.Meta.ArgsPacker
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedTerminationArgument;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_checkCodomains___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3;
lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6;
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1;
lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___boxed(lean_object**);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9;
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7;
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(x_1, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_7);
if (x_9 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
case 6:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
case 7:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_17);
if (x_19 == 0)
{
x_2 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_23);
if (x_26 == 0)
{
x_2 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
x_2 = x_30;
goto _start;
}
case 11:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
default: 
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The termination argument's type must not depend on the ", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function's varying parameters, but ", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'s termination argument does:", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try using `sizeOf` explicitly", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_size(x_4);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1(x_13, x_14, x_4);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_15, x_5);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = l_Lean_MessageData_ofName(x_2);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_3);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_18, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_17, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_17, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_17, 0);
lean_dec(x_32);
x_33 = lean_array_fget(x_24, x_25);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_25, x_34);
lean_dec(x_25);
lean_ctor_set(x_17, 1, x_35);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_19, 2);
lean_inc(x_38);
x_39 = lean_nat_dec_lt(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_12);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_19, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_19, 0);
lean_dec(x_44);
x_45 = lean_array_fget(x_36, x_37);
x_46 = lean_nat_add(x_37, x_34);
lean_dec(x_37);
lean_ctor_set(x_19, 1, x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_1);
x_48 = l_Lean_Expr_beta(x_47, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = lean_infer_type(x_48, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_45);
lean_inc(x_50);
x_53 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed), 12, 3);
lean_closure_set(x_53, 0, x_33);
lean_closure_set(x_53, 1, x_15);
lean_closure_set(x_53, 2, x_50);
x_54 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_50, x_52, x_53, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_push(x_22, x_56);
lean_ctor_set(x_16, 1, x_58);
x_59 = 1;
x_60 = lean_usize_add(x_4, x_59);
x_4 = x_60;
x_12 = x_57;
goto _start;
}
else
{
uint8_t x_62; 
lean_dec(x_19);
lean_dec(x_17);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_55, 0);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_55);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_19);
lean_dec(x_45);
lean_dec(x_17);
lean_dec(x_33);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
return x_49;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_49, 0);
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_49);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_19);
x_70 = lean_array_fget(x_36, x_37);
x_71 = lean_nat_add(x_37, x_34);
lean_dec(x_37);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_38);
x_73 = lean_ctor_get(x_33, 1);
lean_inc(x_73);
lean_inc(x_1);
x_74 = l_Lean_Expr_beta(x_73, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = lean_infer_type(x_74, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_70);
lean_inc(x_76);
x_79 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed), 12, 3);
lean_closure_set(x_79, 0, x_33);
lean_closure_set(x_79, 1, x_15);
lean_closure_set(x_79, 2, x_76);
x_80 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_81 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_76, x_78, x_79, x_80, x_6, x_7, x_8, x_9, x_10, x_11, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_array_push(x_22, x_82);
lean_ctor_set(x_16, 1, x_84);
lean_ctor_set(x_5, 0, x_72);
x_85 = 1;
x_86 = lean_usize_add(x_4, x_85);
x_4 = x_86;
x_12 = x_83;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_72);
lean_dec(x_17);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_90 = x_81;
} else {
 lean_dec_ref(x_81);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_17);
lean_dec(x_33);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_17);
x_96 = lean_array_fget(x_24, x_25);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_25, x_97);
lean_dec(x_25);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_24);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_26);
x_100 = lean_ctor_get(x_19, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_19, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_19, 2);
lean_inc(x_102);
x_103 = lean_nat_dec_lt(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_99);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_5);
lean_ctor_set(x_104, 1, x_12);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_105 = x_19;
} else {
 lean_dec_ref(x_19);
 x_105 = lean_box(0);
}
x_106 = lean_array_fget(x_100, x_101);
x_107 = lean_nat_add(x_101, x_97);
lean_dec(x_101);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 3, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_102);
x_109 = lean_ctor_get(x_96, 1);
lean_inc(x_109);
lean_inc(x_1);
x_110 = l_Lean_Expr_beta(x_109, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_111 = lean_infer_type(x_110, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_106);
lean_inc(x_112);
x_115 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed), 12, 3);
lean_closure_set(x_115, 0, x_96);
lean_closure_set(x_115, 1, x_15);
lean_closure_set(x_115, 2, x_112);
x_116 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_117 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_112, x_114, x_115, x_116, x_6, x_7, x_8, x_9, x_10, x_11, x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; size_t x_121; size_t x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_array_push(x_22, x_118);
lean_ctor_set(x_16, 1, x_120);
lean_ctor_set(x_16, 0, x_99);
lean_ctor_set(x_5, 0, x_108);
x_121 = 1;
x_122 = lean_usize_add(x_4, x_121);
x_4 = x_122;
x_12 = x_119;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_108);
lean_dec(x_99);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_126 = x_117;
} else {
 lean_dec_ref(x_117);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_96);
lean_free_object(x_16);
lean_dec(x_22);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_130 = x_111;
} else {
 lean_dec_ref(x_111);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_16, 1);
lean_inc(x_132);
lean_dec(x_16);
x_133 = lean_ctor_get(x_17, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_17, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_17, 2);
lean_inc(x_135);
x_136 = lean_nat_dec_lt(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_17);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_5, 1, x_137);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_12);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_139 = x_17;
} else {
 lean_dec_ref(x_17);
 x_139 = lean_box(0);
}
x_140 = lean_array_fget(x_133, x_134);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_134, x_141);
lean_dec(x_134);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_133);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_135);
x_144 = lean_ctor_get(x_19, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_19, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_19, 2);
lean_inc(x_146);
x_147 = lean_nat_dec_lt(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_140);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_132);
lean_ctor_set(x_5, 1, x_148);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_5);
lean_ctor_set(x_149, 1, x_12);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_150 = x_19;
} else {
 lean_dec_ref(x_19);
 x_150 = lean_box(0);
}
x_151 = lean_array_fget(x_144, x_145);
x_152 = lean_nat_add(x_145, x_141);
lean_dec(x_145);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 3, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_146);
x_154 = lean_ctor_get(x_140, 1);
lean_inc(x_154);
lean_inc(x_1);
x_155 = l_Lean_Expr_beta(x_154, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_156 = lean_infer_type(x_155, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_151);
lean_inc(x_157);
x_160 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed), 12, 3);
lean_closure_set(x_160, 0, x_140);
lean_closure_set(x_160, 1, x_15);
lean_closure_set(x_160, 2, x_157);
x_161 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_162 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_157, x_159, x_160, x_161, x_6, x_7, x_8, x_9, x_10, x_11, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; size_t x_167; size_t x_168; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_array_push(x_132, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_143);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_5, 1, x_166);
lean_ctor_set(x_5, 0, x_153);
x_167 = 1;
x_168 = lean_usize_add(x_4, x_167);
x_4 = x_168;
x_12 = x_164;
goto _start;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_153);
lean_dec(x_143);
lean_dec(x_132);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_172 = x_162;
} else {
 lean_dec_ref(x_162);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_132);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_174 = lean_ctor_get(x_156, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_156, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_176 = x_156;
} else {
 lean_dec_ref(x_156);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_178 = lean_ctor_get(x_5, 0);
lean_inc(x_178);
lean_dec(x_5);
x_179 = lean_ctor_get(x_16, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_180 = x_16;
} else {
 lean_dec_ref(x_16);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_17, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_17, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_17, 2);
lean_inc(x_183);
x_184 = lean_nat_dec_lt(x_182, x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_17);
lean_ctor_set(x_185, 1, x_179);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_12);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_188 = x_17;
} else {
 lean_dec_ref(x_17);
 x_188 = lean_box(0);
}
x_189 = lean_array_fget(x_181, x_182);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_182, x_190);
lean_dec(x_182);
if (lean_is_scalar(x_188)) {
 x_192 = lean_alloc_ctor(0, 3, 0);
} else {
 x_192 = x_188;
}
lean_ctor_set(x_192, 0, x_181);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_192, 2, x_183);
x_193 = lean_ctor_get(x_178, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_178, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_178, 2);
lean_inc(x_195);
x_196 = lean_nat_dec_lt(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_189);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_180)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_180;
}
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_179);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_178);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_12);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 x_200 = x_178;
} else {
 lean_dec_ref(x_178);
 x_200 = lean_box(0);
}
x_201 = lean_array_fget(x_193, x_194);
x_202 = lean_nat_add(x_194, x_190);
lean_dec(x_194);
if (lean_is_scalar(x_200)) {
 x_203 = lean_alloc_ctor(0, 3, 0);
} else {
 x_203 = x_200;
}
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_203, 2, x_195);
x_204 = lean_ctor_get(x_189, 1);
lean_inc(x_204);
lean_inc(x_1);
x_205 = l_Lean_Expr_beta(x_204, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_206 = lean_infer_type(x_205, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_201);
lean_inc(x_207);
x_210 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed), 12, 3);
lean_closure_set(x_210, 0, x_189);
lean_closure_set(x_210, 1, x_15);
lean_closure_set(x_210, 2, x_207);
x_211 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_212 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_207, x_209, x_210, x_211, x_6, x_7, x_8, x_9, x_10, x_11, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_array_push(x_179, x_213);
if (lean_is_scalar(x_180)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_180;
}
lean_ctor_set(x_216, 0, x_192);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_203);
lean_ctor_set(x_217, 1, x_216);
x_218 = 1;
x_219 = lean_usize_add(x_4, x_218);
x_4 = x_219;
x_5 = x_217;
x_12 = x_214;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_203);
lean_dec(x_192);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_221 = lean_ctor_get(x_212, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_212, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_223 = x_212;
} else {
 lean_dec_ref(x_212);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_192);
lean_dec(x_189);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_225 = lean_ctor_get(x_206, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_206, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_227 = x_206;
} else {
 lean_dec_ref(x_206);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The termination arguments of mutually recursive functions ", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("must have the same return type, but the termination argument of ", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has type", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("while the termination argument of ", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_12, x_9);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_11, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_11, x_26);
lean_dec(x_11);
x_28 = lean_array_fget(x_4, x_12);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_28);
lean_inc(x_7);
x_29 = l_Lean_Meta_isExprDefEqGuarded(x_7, x_28, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_nat_dec_lt(x_12, x_3);
x_34 = lean_array_get_size(x_1);
x_35 = lean_nat_dec_lt(x_24, x_34);
x_36 = l_Lean_indentExpr(x_7);
x_37 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_nat_dec_lt(x_12, x_34);
lean_dec(x_34);
x_42 = l_Lean_indentExpr(x_28);
if (x_33 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lean_Elab_instInhabitedTerminationArgument;
x_91 = l_outOfBounds___rarg(x_90);
x_43 = x_91;
goto block_89;
}
else
{
lean_object* x_92; 
x_92 = lean_array_fget(x_2, x_12);
x_43 = x_92;
goto block_89;
}
block_89:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
if (x_35 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_instInhabitedName;
x_87 = l_outOfBounds___rarg(x_86);
x_45 = x_87;
goto block_85;
}
else
{
lean_object* x_88; 
x_88 = lean_array_fget(x_1, x_24);
x_45 = x_88;
goto block_85;
}
block_85:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = l_Lean_MessageData_ofName(x_45);
x_47 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
if (x_41 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_12);
x_54 = l_Lean_instInhabitedName;
x_55 = l_outOfBounds___rarg(x_54);
x_56 = l_Lean_MessageData_ofName(x_55);
x_57 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_39);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_44, x_64, x_15, x_16, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_44);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_70 = lean_array_fget(x_1, x_12);
lean_dec(x_12);
x_71 = l_Lean_MessageData_ofName(x_70);
x_72 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_49);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_42);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_39);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_53);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_44, x_79, x_15, x_16, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_44);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_28);
x_93 = lean_ctor_get(x_29, 1);
lean_inc(x_93);
lean_dec(x_29);
x_94 = lean_nat_add(x_12, x_10);
lean_dec(x_12);
x_95 = lean_box(0);
x_11 = x_27;
x_12 = x_94;
x_13 = lean_box(0);
x_14 = x_95;
x_21 = x_93;
goto _start;
}
}
else
{
uint8_t x_97; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_29);
if (x_97 == 0)
{
return x_29;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_29, 0);
x_99 = lean_ctor_get(x_29, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_29);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_14);
lean_ctor_set(x_101, 1, x_21);
return x_101;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_checkCodomains___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_3, x_13, x_12);
x_15 = lean_array_get_size(x_4);
lean_inc(x_15);
lean_inc(x_4);
x_16 = l_Array_toSubarray___rarg(x_4, x_13, x_15);
x_17 = l_Lean_Elab_WF_checkCodomains___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_1);
x_21 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3(x_2, x_1, x_20, x_21, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_13, x_27);
x_29 = lean_unsigned_to_nat(1u);
lean_inc(x_27);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
if (x_28 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_instInhabitedExpr;
x_44 = l_outOfBounds___rarg(x_43);
x_31 = x_44;
goto block_42;
}
else
{
lean_object* x_45; 
x_45 = lean_array_fget(x_26, x_13);
x_31 = x_45;
goto block_42;
}
block_42:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
lean_inc(x_31);
lean_inc(x_27);
x_33 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4(x_1, x_4, x_15, x_26, x_27, x_30, x_31, x_29, x_27, x_29, x_27, x_29, lean_box(0), x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_6);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_4);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_31);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_checkCodomains___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Elab_WF_checkCodomains___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_checkCodomains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_WF_checkCodomains(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_1);
x_10 = l_Lean_Expr_beta(x_9, x_1);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WellFoundedRelation", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invImage", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_getLevel(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_size(x_2);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1(x_17, x_18, x_2);
lean_inc(x_3);
x_20 = l_Lean_Meta_ArgsPacker_arities(x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Elab_WF_checkCodomains(x_19, x_4, x_20, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_24 = l_Lean_Meta_getLevel(x_22, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_size(x_5);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2(x_4, x_27, x_18, x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Meta_ArgsPacker_uncurryND(x_3, x_28, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_28);
lean_dec(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2;
lean_inc(x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_33);
lean_inc(x_22);
x_36 = l_Lean_Expr_app___override(x_35, x_22);
x_37 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_Lean_Meta_synthInstance(x_36, x_37, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_33);
x_42 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4;
x_43 = l_Lean_Expr_const___override(x_42, x_41);
x_44 = l_Lean_mkApp4(x_43, x_1, x_22, x_30, x_39);
x_45 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_8(x_6, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
return x_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
return x_24;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_24, 0);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_24);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
return x_21;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_21, 0);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_21);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_14);
if (x_65 == 0)
{
return x_14;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_14, 0);
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_14);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 13, 6);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_7);
x_16 = l_Lean_Elab_Term_withDeclName___rarg(x_2, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg), 14, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel___spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationArgument(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationArgument(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_checkCodomains___spec__3___lambda__2___closed__11);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__4);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__5);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__6);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__7);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__8);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__9);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_checkCodomains___spec__4___closed__10);
l_Lean_Elab_WF_checkCodomains___closed__1 = _init_l_Lean_Elab_WF_checkCodomains___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_checkCodomains___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
