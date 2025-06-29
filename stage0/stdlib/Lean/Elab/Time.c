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
static lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__3;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__0;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__6;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__7;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__5;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2;
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__4;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("timeCmd", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__2;
x_2 = l_Lean_Elab_Time_elabTimeCmd___closed__1;
x_3 = l_Lean_Elab_Time_elabTimeCmd___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("time: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ms", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Time_elabTimeCmd___closed__3;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_io_mono_ms_now(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Command_elabCommand(x_12, x_2, x_3, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_io_mono_ms_now(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_Elab_Time_elabTimeCmd___closed__5;
x_24 = lean_nat_sub(x_19, x_9);
lean_dec(x_9);
lean_dec(x_19);
x_25 = l_Nat_reprFast(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_23);
x_28 = l_Lean_Elab_Time_elabTimeCmd___closed__7;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_17);
x_29 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_22, x_13, x_2, x_3, x_20);
lean_dec(x_3);
lean_dec(x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
lean_dec(x_1);
x_34 = l_Lean_Elab_Time_elabTimeCmd___closed__5;
x_35 = lean_nat_sub(x_30, x_9);
lean_dec(x_9);
lean_dec(x_30);
x_36 = l_Nat_reprFast(x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Time_elabTimeCmd___closed__7;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_40);
lean_ctor_set(x_13, 0, x_39);
x_41 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_33, x_13, x_2, x_3, x_31);
lean_dec(x_3);
lean_dec(x_33);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_io_mono_ms_now(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
lean_dec(x_1);
x_49 = l_Lean_Elab_Time_elabTimeCmd___closed__5;
x_50 = lean_nat_sub(x_44, x_9);
lean_dec(x_9);
lean_dec(x_44);
x_51 = l_Nat_reprFast(x_50);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_46;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Time_elabTimeCmd___closed__7;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_48, x_56, x_2, x_3, x_45);
lean_dec(x_3);
lean_dec(x_48);
return x_57;
}
}
else
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Time", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabTimeCmd", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3;
x_2 = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2;
x_3 = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1;
x_4 = l_Lean_Elab_Time_elabTimeCmd___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0;
x_3 = l_Lean_Elab_Time_elabTimeCmd___closed__3;
x_4 = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
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
l_Lean_Elab_Time_elabTimeCmd___closed__0 = _init_l_Lean_Elab_Time_elabTimeCmd___closed__0();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___closed__0);
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
l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0 = _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0);
l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1 = _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1);
l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2 = _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2);
l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3 = _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3);
l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4 = _init_l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__4);
if (builtin) {res = l_Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
