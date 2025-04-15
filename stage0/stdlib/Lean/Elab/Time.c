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
lean_object* l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
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
x_29 = 0;
x_30 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_9, x_12, x_28, x_29, x_2, x_3, x_21);
lean_dec(x_3);
lean_dec(x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_nat_sub(x_31, x_14);
lean_dec(x_14);
lean_dec(x_31);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Time_elabTimeCmd___closed__8;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_39);
lean_ctor_set(x_12, 0, x_38);
x_40 = 0;
x_41 = 0;
x_42 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_9, x_12, x_40, x_41, x_2, x_3, x_32);
lean_dec(x_3);
lean_dec(x_9);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_49 = l_Lean_Elab_Command_elabCommand(x_11, x_2, x_3, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_io_mono_ms_now(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_nat_sub(x_52, x_47);
lean_dec(x_47);
lean_dec(x_52);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_54;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_Time_elabTimeCmd___closed__8;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = 0;
x_64 = 0;
x_65 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_9, x_62, x_63, x_64, x_2, x_3, x_53);
lean_dec(x_3);
lean_dec(x_9);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_68 = x_49;
} else {
 lean_dec_ref(x_49);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
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
