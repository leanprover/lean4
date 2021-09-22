// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Change
// Imports: Init Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Conv.Basic
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
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__14;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__10;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__16;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__12;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6;
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__8;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__9;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__13;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalChange___closed__6;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_changeLhs(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__2;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__4;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Conv");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__6;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("change");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__8;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'change' conv tactic, term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nis not definitionally equal to current left-hand-side");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Conv_evalChange___closed__10;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Elab_Tactic_Conv_getLhs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_9, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_7, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_26 = lean_infer_type(x_17, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_15, x_29, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_32);
x_34 = l_Lean_Meta_getMVars(x_32, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_filterOldMVars(x_35, x_25, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_25);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_32);
x_42 = l_Lean_Meta_isExprDefEqGuarded(x_32, x_17, x_6, x_7, x_8, x_9, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_indentExpr(x_32);
x_47 = l_Lean_Elab_Tactic_Conv_evalChange___closed__12;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_Tactic_Conv_evalChange___closed__14;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_17);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_Conv_evalChange___closed__16;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_dec(x_42);
x_61 = l_Lean_Elab_Tactic_Conv_changeLhs(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_40, 0);
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_40);
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
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_34);
if (x_66 == 0)
{
return x_34;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_34, 0);
x_68 = lean_ctor_get(x_34, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_34);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_31);
if (x_70 == 0)
{
return x_31;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_31, 0);
x_72 = lean_ctor_get(x_31, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_31);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_26);
if (x_74 == 0)
{
return x_26;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_26, 0);
x_76 = lean_ctor_get(x_26, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_26);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_16);
if (x_78 == 0)
{
return x_16;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_16, 0);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_16);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalChange___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Conv_evalChange___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalChange___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3;
x_2 = l_Lean_Elab_Tactic_Conv_evalChange___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalChange");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalChange), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalChange___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Change(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(lean_io_mk_world());
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
l_Lean_Elab_Tactic_Conv_evalChange___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__7);
l_Lean_Elab_Tactic_Conv_evalChange___closed__8 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__8);
l_Lean_Elab_Tactic_Conv_evalChange___closed__9 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__9);
l_Lean_Elab_Tactic_Conv_evalChange___closed__10 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__10);
l_Lean_Elab_Tactic_Conv_evalChange___closed__11 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__11);
l_Lean_Elab_Tactic_Conv_evalChange___closed__12 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__12);
l_Lean_Elab_Tactic_Conv_evalChange___closed__13 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__13);
l_Lean_Elab_Tactic_Conv_evalChange___closed__14 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__14);
l_Lean_Elab_Tactic_Conv_evalChange___closed__15 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__15);
l_Lean_Elab_Tactic_Conv_evalChange___closed__16 = _init_l_Lean_Elab_Tactic_Conv_evalChange___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalChange___closed__16);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalChange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
