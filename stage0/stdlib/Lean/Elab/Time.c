// Lean compiler output
// Module: Lean.Elab.Time
// Imports: Lean.Elab.Command
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__6;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__7;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("timeCmd", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__1;
x_2 = l_Lean_Elab_Time_elabTimeCmd___closed__2;
x_3 = l_Lean_Elab_Time_elabTimeCmd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("time: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ms", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Time_elabTimeCmd___closed__4;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_io_mono_ms_now(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Elab_Command_elabCommand(x_11, x_2, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_io_mono_ms_now(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_nat_sub(x_20, x_14);
lean_dec(x_14);
lean_dec(x_20);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = l_Lean_Elab_Time_elabTimeCmd___closed__8;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_18);
x_28 = 0;
x_29 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_9, x_12, x_28, x_2, x_3, x_21);
lean_dec(x_3);
lean_dec(x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_nat_sub(x_30, x_14);
lean_dec(x_14);
lean_dec(x_30);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_Time_elabTimeCmd___closed__8;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_37);
x_39 = 0;
x_40 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_9, x_12, x_39, x_2, x_3, x_31);
lean_dec(x_3);
lean_dec(x_9);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Lean_Elab_Command_elabCommand(x_11, x_2, x_3, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_io_mono_ms_now(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_nat_sub(x_50, x_45);
lean_dec(x_45);
lean_dec(x_50);
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_52;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Time_elabTimeCmd___closed__8;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = 0;
x_62 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_9, x_60, x_61, x_2, x_3, x_51);
lean_dec(x_3);
lean_dec(x_9);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_65 = x_47;
} else {
 lean_dec_ref(x_47);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Time", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabTimeCmd", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5;
x_3 = l_Lean_Elab_Time_elabTimeCmd___closed__4;
x_4 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Time(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Time_elabTimeCmd___spec__1___rarg___closed__2);
l_Lean_Elab_Time_elabTimeCmd___closed__1 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__1);
l_Lean_Elab_Time_elabTimeCmd___closed__2 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__2);
l_Lean_Elab_Time_elabTimeCmd___closed__3 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__3();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__3);
l_Lean_Elab_Time_elabTimeCmd___closed__4 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__4();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__4);
l_Lean_Elab_Time_elabTimeCmd___closed__5 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__5();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__5);
l_Lean_Elab_Time_elabTimeCmd___closed__6 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__6();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__6);
l_Lean_Elab_Time_elabTimeCmd___closed__7 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__7();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__7);
l_Lean_Elab_Time_elabTimeCmd___closed__8 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__8();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__8);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__5);
l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
