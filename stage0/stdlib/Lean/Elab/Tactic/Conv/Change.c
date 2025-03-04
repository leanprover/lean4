// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Change
// Imports: Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Change Lean.Elab.Tactic.Conv.Basic
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
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_elabChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__1;
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6;
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1;
lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Elab_Tactic_Conv_getLhs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_elabChange(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
x_22 = l_Lean_Meta_getMVars(x_20, x_6, x_7, x_8, x_9, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Tactic_filterOldMVars(x_23, x_18, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_18);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Tactic_Conv_changeLhs(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Conv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("change", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__1;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__2;
x_3 = l_Lean_Elab_Tactic_Conv_evalChange___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalChange___closed__4;
x_5 = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Conv_evalChange___closed__6;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalChange___lambda__1), 10, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Tactic_withMainContext___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalChange", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1;
x_3 = l_Lean_Elab_Tactic_Conv_evalChange___closed__3;
x_4 = l_Lean_Elab_Tactic_Conv_evalChange___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalChange), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4;
x_3 = l_Lean_Elab_Tactic_Conv_evalChange___closed__6;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(63u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Change(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Change(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Change(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Conv_evalChange___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__1);
l_Lean_Elab_Tactic_Conv_evalChange___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__2);
l_Lean_Elab_Tactic_Conv_evalChange___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__3);
l_Lean_Elab_Tactic_Conv_evalChange___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__4);
l_Lean_Elab_Tactic_Conv_evalChange___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__5);
l_Lean_Elab_Tactic_Conv_evalChange___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
