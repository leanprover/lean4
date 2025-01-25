// Lean compiler output
// Module: Lean.Elab.Tactic.DiscrTreeKey
// Imports: Init.Tactics Lean.Elab.Command Lean.Meta.Tactic.Simp.SimpTheorems
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
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3;
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8;
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4;
lean_object* l_Lean_log___at_Lean_Elab_Term_exceptionToSorry___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2;
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7;
static uint64_t l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_21 = 2;
lean_ctor_set_uint8(x_9, 9, x_21);
x_22 = 2;
x_23 = lean_uint64_shift_right(x_10, x_22);
x_24 = lean_uint64_shift_left(x_23, x_22);
x_25 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1;
x_26 = lean_uint64_lor(x_24, x_25);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_27 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set(x_27, 5, x_16);
lean_ctor_set(x_27, 6, x_17);
lean_ctor_set_uint64(x_27, sizeof(void*)*7, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 10, x_20);
x_28 = 1;
x_29 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_28, x_8, x_29, x_27, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Meta_whnfR(x_34, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_35) == 0)
{
if (x_2 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
x_39 = l_Lean_Meta_DiscrTree_mkPath(x_36, x_38, x_3, x_4, x_5, x_6, x_37);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_41 = lean_ctor_get(x_3, 6);
lean_dec(x_41);
x_42 = lean_ctor_get(x_3, 5);
lean_dec(x_42);
x_43 = lean_ctor_get(x_3, 4);
lean_dec(x_43);
x_44 = lean_ctor_get(x_3, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_51 = lean_unsigned_to_nat(3u);
x_52 = l_Lean_Expr_isAppOfArity(x_48, x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_54 = lean_unsigned_to_nat(2u);
x_55 = l_Lean_Expr_isAppOfArity(x_48, x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_57 = l_Lean_Expr_isAppOfArity(x_48, x_56, x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Expr_isAppOfArity(x_48, x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; uint8_t x_64; lean_object* x_65; 
x_61 = l_Lean_Meta_simpGlobalConfig;
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_61, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_62);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_63);
x_64 = 0;
x_65 = l_Lean_Meta_DiscrTree_mkPath(x_48, x_64, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
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
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
x_75 = l_Lean_Expr_isAppOfArity(x_74, x_50, x_51);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint64_t x_78; uint8_t x_79; lean_object* x_80; 
x_76 = l_Lean_Meta_simpGlobalConfig;
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint64(x_76, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_77);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_78);
x_79 = 0;
x_80 = l_Lean_Meta_DiscrTree_mkPath(x_74, x_79, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
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
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint64_t x_93; uint8_t x_94; lean_object* x_95; 
x_89 = l_Lean_Expr_appFn_x21(x_74);
lean_dec(x_74);
x_90 = l_Lean_Expr_appArg_x21(x_89);
lean_dec(x_89);
x_91 = l_Lean_Meta_simpGlobalConfig;
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get_uint64(x_91, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_92);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_93);
x_94 = 0;
x_95 = l_Lean_Meta_DiscrTree_mkPath(x_90, x_94, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
return x_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; uint8_t x_109; lean_object* x_110; 
x_104 = l_Lean_Expr_appFn_x21(x_48);
lean_dec(x_48);
x_105 = l_Lean_Expr_appArg_x21(x_104);
lean_dec(x_104);
x_106 = l_Lean_Meta_simpGlobalConfig;
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint64(x_106, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_107);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_108);
x_109 = 0;
x_110 = l_Lean_Meta_DiscrTree_mkPath(x_105, x_109, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_110);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; uint8_t x_124; lean_object* x_125; 
x_119 = l_Lean_Expr_appFn_x21(x_48);
lean_dec(x_48);
x_120 = l_Lean_Expr_appArg_x21(x_119);
lean_dec(x_119);
x_121 = l_Lean_Meta_simpGlobalConfig;
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get_uint64(x_121, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_122);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_123);
x_124 = 0;
x_125 = l_Lean_Meta_DiscrTree_mkPath(x_120, x_124, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_125);
if (x_130 == 0)
{
return x_125;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_125, 0);
x_132 = lean_ctor_get(x_125, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_125);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint64_t x_138; uint8_t x_139; lean_object* x_140; 
x_134 = l_Lean_Expr_appFn_x21(x_48);
lean_dec(x_48);
x_135 = l_Lean_Expr_appArg_x21(x_134);
lean_dec(x_134);
x_136 = l_Lean_Meta_simpGlobalConfig;
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint64(x_136, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_137);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_138);
x_139 = 0;
x_140 = l_Lean_Meta_DiscrTree_mkPath(x_135, x_139, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_140);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_140);
if (x_145 == 0)
{
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_140, 0);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_140);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_3);
x_149 = lean_ctor_get(x_35, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_35, 1);
lean_inc(x_150);
lean_dec(x_35);
x_151 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_152 = lean_unsigned_to_nat(3u);
x_153 = l_Lean_Expr_isAppOfArity(x_149, x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_155 = lean_unsigned_to_nat(2u);
x_156 = l_Lean_Expr_isAppOfArity(x_149, x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_158 = l_Lean_Expr_isAppOfArity(x_149, x_157, x_152);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_160 = lean_unsigned_to_nat(1u);
x_161 = l_Lean_Expr_isAppOfArity(x_149, x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; uint64_t x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_162 = l_Lean_Meta_simpGlobalConfig;
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get_uint64(x_162, sizeof(void*)*1);
x_165 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_12);
lean_ctor_set(x_165, 2, x_13);
lean_ctor_set(x_165, 3, x_14);
lean_ctor_set(x_165, 4, x_15);
lean_ctor_set(x_165, 5, x_16);
lean_ctor_set(x_165, 6, x_17);
lean_ctor_set_uint64(x_165, sizeof(void*)*7, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_165, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_165, sizeof(void*)*7 + 10, x_20);
x_166 = 0;
x_167 = l_Lean_Meta_DiscrTree_mkPath(x_149, x_166, x_165, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = l_Lean_Expr_appArg_x21(x_149);
lean_dec(x_149);
x_177 = l_Lean_Expr_isAppOfArity(x_176, x_151, x_152);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; uint64_t x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_178 = l_Lean_Meta_simpGlobalConfig;
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get_uint64(x_178, sizeof(void*)*1);
x_181 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_12);
lean_ctor_set(x_181, 2, x_13);
lean_ctor_set(x_181, 3, x_14);
lean_ctor_set(x_181, 4, x_15);
lean_ctor_set(x_181, 5, x_16);
lean_ctor_set(x_181, 6, x_17);
lean_ctor_set_uint64(x_181, sizeof(void*)*7, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_181, sizeof(void*)*7 + 10, x_20);
x_182 = 0;
x_183 = l_Lean_Meta_DiscrTree_mkPath(x_176, x_182, x_181, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_190 = x_183;
} else {
 lean_dec_ref(x_183);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint64_t x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_192 = l_Lean_Expr_appFn_x21(x_176);
lean_dec(x_176);
x_193 = l_Lean_Expr_appArg_x21(x_192);
lean_dec(x_192);
x_194 = l_Lean_Meta_simpGlobalConfig;
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get_uint64(x_194, sizeof(void*)*1);
x_197 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_12);
lean_ctor_set(x_197, 2, x_13);
lean_ctor_set(x_197, 3, x_14);
lean_ctor_set(x_197, 4, x_15);
lean_ctor_set(x_197, 5, x_16);
lean_ctor_set(x_197, 6, x_17);
lean_ctor_set_uint64(x_197, sizeof(void*)*7, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_197, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_197, sizeof(void*)*7 + 10, x_20);
x_198 = 0;
x_199 = l_Lean_Meta_DiscrTree_mkPath(x_193, x_198, x_197, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint64_t x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_208 = l_Lean_Expr_appFn_x21(x_149);
lean_dec(x_149);
x_209 = l_Lean_Expr_appArg_x21(x_208);
lean_dec(x_208);
x_210 = l_Lean_Meta_simpGlobalConfig;
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get_uint64(x_210, sizeof(void*)*1);
x_213 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_12);
lean_ctor_set(x_213, 2, x_13);
lean_ctor_set(x_213, 3, x_14);
lean_ctor_set(x_213, 4, x_15);
lean_ctor_set(x_213, 5, x_16);
lean_ctor_set(x_213, 6, x_17);
lean_ctor_set_uint64(x_213, sizeof(void*)*7, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 10, x_20);
x_214 = 0;
x_215 = l_Lean_Meta_DiscrTree_mkPath(x_209, x_214, x_213, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_222 = x_215;
} else {
 lean_dec_ref(x_215);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint64_t x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_224 = l_Lean_Expr_appFn_x21(x_149);
lean_dec(x_149);
x_225 = l_Lean_Expr_appArg_x21(x_224);
lean_dec(x_224);
x_226 = l_Lean_Meta_simpGlobalConfig;
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get_uint64(x_226, sizeof(void*)*1);
x_229 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_12);
lean_ctor_set(x_229, 2, x_13);
lean_ctor_set(x_229, 3, x_14);
lean_ctor_set(x_229, 4, x_15);
lean_ctor_set(x_229, 5, x_16);
lean_ctor_set(x_229, 6, x_17);
lean_ctor_set_uint64(x_229, sizeof(void*)*7, x_228);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 10, x_20);
x_230 = 0;
x_231 = l_Lean_Meta_DiscrTree_mkPath(x_225, x_230, x_229, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_231, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_238 = x_231;
} else {
 lean_dec_ref(x_231);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint64_t x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_240 = l_Lean_Expr_appFn_x21(x_149);
lean_dec(x_149);
x_241 = l_Lean_Expr_appArg_x21(x_240);
lean_dec(x_240);
x_242 = l_Lean_Meta_simpGlobalConfig;
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get_uint64(x_242, sizeof(void*)*1);
x_245 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_12);
lean_ctor_set(x_245, 2, x_13);
lean_ctor_set(x_245, 3, x_14);
lean_ctor_set(x_245, 4, x_15);
lean_ctor_set(x_245, 5, x_16);
lean_ctor_set(x_245, 6, x_17);
lean_ctor_set_uint64(x_245, sizeof(void*)*7, x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_245, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_245, sizeof(void*)*7 + 10, x_20);
x_246 = 0;
x_247 = l_Lean_Meta_DiscrTree_mkPath(x_241, x_246, x_245, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_247, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = !lean_is_exclusive(x_35);
if (x_256 == 0)
{
return x_35;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_35, 0);
x_258 = lean_ctor_get(x_35, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_35);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_260 = !lean_is_exclusive(x_30);
if (x_260 == 0)
{
return x_30;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_30, 0);
x_262 = lean_ctor_get(x_30, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_30);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; lean_object* x_284; uint64_t x_285; uint64_t x_286; uint64_t x_287; uint64_t x_288; uint64_t x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; 
x_264 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_265 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_266 = lean_ctor_get_uint8(x_9, 0);
x_267 = lean_ctor_get_uint8(x_9, 1);
x_268 = lean_ctor_get_uint8(x_9, 2);
x_269 = lean_ctor_get_uint8(x_9, 3);
x_270 = lean_ctor_get_uint8(x_9, 4);
x_271 = lean_ctor_get_uint8(x_9, 5);
x_272 = lean_ctor_get_uint8(x_9, 6);
x_273 = lean_ctor_get_uint8(x_9, 7);
x_274 = lean_ctor_get_uint8(x_9, 8);
x_275 = lean_ctor_get_uint8(x_9, 10);
x_276 = lean_ctor_get_uint8(x_9, 11);
x_277 = lean_ctor_get_uint8(x_9, 12);
x_278 = lean_ctor_get_uint8(x_9, 13);
x_279 = lean_ctor_get_uint8(x_9, 14);
x_280 = lean_ctor_get_uint8(x_9, 15);
x_281 = lean_ctor_get_uint8(x_9, 16);
x_282 = lean_ctor_get_uint8(x_9, 17);
lean_dec(x_9);
x_283 = 2;
x_284 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_284, 0, x_266);
lean_ctor_set_uint8(x_284, 1, x_267);
lean_ctor_set_uint8(x_284, 2, x_268);
lean_ctor_set_uint8(x_284, 3, x_269);
lean_ctor_set_uint8(x_284, 4, x_270);
lean_ctor_set_uint8(x_284, 5, x_271);
lean_ctor_set_uint8(x_284, 6, x_272);
lean_ctor_set_uint8(x_284, 7, x_273);
lean_ctor_set_uint8(x_284, 8, x_274);
lean_ctor_set_uint8(x_284, 9, x_283);
lean_ctor_set_uint8(x_284, 10, x_275);
lean_ctor_set_uint8(x_284, 11, x_276);
lean_ctor_set_uint8(x_284, 12, x_277);
lean_ctor_set_uint8(x_284, 13, x_278);
lean_ctor_set_uint8(x_284, 14, x_279);
lean_ctor_set_uint8(x_284, 15, x_280);
lean_ctor_set_uint8(x_284, 16, x_281);
lean_ctor_set_uint8(x_284, 17, x_282);
x_285 = 2;
x_286 = lean_uint64_shift_right(x_10, x_285);
x_287 = lean_uint64_shift_left(x_286, x_285);
x_288 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1;
x_289 = lean_uint64_lor(x_287, x_288);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_290 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_12);
lean_ctor_set(x_290, 2, x_13);
lean_ctor_set(x_290, 3, x_14);
lean_ctor_set(x_290, 4, x_15);
lean_ctor_set(x_290, 5, x_16);
lean_ctor_set(x_290, 6, x_17);
lean_ctor_set_uint64(x_290, sizeof(void*)*7, x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_290, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_290, sizeof(void*)*7 + 10, x_265);
x_291 = 1;
x_292 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_293 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_291, x_8, x_292, x_290, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_298 = l_Lean_Meta_whnfR(x_297, x_3, x_4, x_5, x_6, x_296);
if (lean_obj_tag(x_298) == 0)
{
if (x_2 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = 0;
x_302 = l_Lean_Meta_DiscrTree_mkPath(x_299, x_301, x_3, x_4, x_5, x_6, x_300);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_303 = x_3;
} else {
 lean_dec_ref(x_3);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_298, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_298, 1);
lean_inc(x_305);
lean_dec(x_298);
x_306 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_307 = lean_unsigned_to_nat(3u);
x_308 = l_Lean_Expr_isAppOfArity(x_304, x_306, x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_310 = lean_unsigned_to_nat(2u);
x_311 = l_Lean_Expr_isAppOfArity(x_304, x_309, x_310);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_313 = l_Lean_Expr_isAppOfArity(x_304, x_312, x_307);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_315 = lean_unsigned_to_nat(1u);
x_316 = l_Lean_Expr_isAppOfArity(x_304, x_314, x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; uint64_t x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_317 = l_Lean_Meta_simpGlobalConfig;
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get_uint64(x_317, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_320 = lean_alloc_ctor(0, 7, 11);
} else {
 x_320 = x_303;
}
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_12);
lean_ctor_set(x_320, 2, x_13);
lean_ctor_set(x_320, 3, x_14);
lean_ctor_set(x_320, 4, x_15);
lean_ctor_set(x_320, 5, x_16);
lean_ctor_set(x_320, 6, x_17);
lean_ctor_set_uint64(x_320, sizeof(void*)*7, x_319);
lean_ctor_set_uint8(x_320, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_320, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_320, sizeof(void*)*7 + 10, x_265);
x_321 = 0;
x_322 = l_Lean_Meta_DiscrTree_mkPath(x_304, x_321, x_320, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_325 = x_322;
} else {
 lean_dec_ref(x_322);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_322, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_322, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_329 = x_322;
} else {
 lean_dec_ref(x_322);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; uint8_t x_332; 
x_331 = l_Lean_Expr_appArg_x21(x_304);
lean_dec(x_304);
x_332 = l_Lean_Expr_isAppOfArity(x_331, x_306, x_307);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; uint64_t x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; 
x_333 = l_Lean_Meta_simpGlobalConfig;
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get_uint64(x_333, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_336 = lean_alloc_ctor(0, 7, 11);
} else {
 x_336 = x_303;
}
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_12);
lean_ctor_set(x_336, 2, x_13);
lean_ctor_set(x_336, 3, x_14);
lean_ctor_set(x_336, 4, x_15);
lean_ctor_set(x_336, 5, x_16);
lean_ctor_set(x_336, 6, x_17);
lean_ctor_set_uint64(x_336, sizeof(void*)*7, x_335);
lean_ctor_set_uint8(x_336, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_336, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_336, sizeof(void*)*7 + 10, x_265);
x_337 = 0;
x_338 = l_Lean_Meta_DiscrTree_mkPath(x_331, x_337, x_336, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_338, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_338, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_345 = x_338;
} else {
 lean_dec_ref(x_338);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint64_t x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; 
x_347 = l_Lean_Expr_appFn_x21(x_331);
lean_dec(x_331);
x_348 = l_Lean_Expr_appArg_x21(x_347);
lean_dec(x_347);
x_349 = l_Lean_Meta_simpGlobalConfig;
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get_uint64(x_349, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_352 = lean_alloc_ctor(0, 7, 11);
} else {
 x_352 = x_303;
}
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_12);
lean_ctor_set(x_352, 2, x_13);
lean_ctor_set(x_352, 3, x_14);
lean_ctor_set(x_352, 4, x_15);
lean_ctor_set(x_352, 5, x_16);
lean_ctor_set(x_352, 6, x_17);
lean_ctor_set_uint64(x_352, sizeof(void*)*7, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_352, sizeof(void*)*7 + 10, x_265);
x_353 = 0;
x_354 = l_Lean_Meta_DiscrTree_mkPath(x_348, x_353, x_352, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_ctor_get(x_354, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_354, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_361 = x_354;
} else {
 lean_dec_ref(x_354);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint64_t x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_363 = l_Lean_Expr_appFn_x21(x_304);
lean_dec(x_304);
x_364 = l_Lean_Expr_appArg_x21(x_363);
lean_dec(x_363);
x_365 = l_Lean_Meta_simpGlobalConfig;
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get_uint64(x_365, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_368 = lean_alloc_ctor(0, 7, 11);
} else {
 x_368 = x_303;
}
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_12);
lean_ctor_set(x_368, 2, x_13);
lean_ctor_set(x_368, 3, x_14);
lean_ctor_set(x_368, 4, x_15);
lean_ctor_set(x_368, 5, x_16);
lean_ctor_set(x_368, 6, x_17);
lean_ctor_set_uint64(x_368, sizeof(void*)*7, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_368, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_368, sizeof(void*)*7 + 10, x_265);
x_369 = 0;
x_370 = l_Lean_Meta_DiscrTree_mkPath(x_364, x_369, x_368, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_370, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_370, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_377 = x_370;
} else {
 lean_dec_ref(x_370);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint64_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_379 = l_Lean_Expr_appFn_x21(x_304);
lean_dec(x_304);
x_380 = l_Lean_Expr_appArg_x21(x_379);
lean_dec(x_379);
x_381 = l_Lean_Meta_simpGlobalConfig;
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get_uint64(x_381, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_384 = lean_alloc_ctor(0, 7, 11);
} else {
 x_384 = x_303;
}
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_12);
lean_ctor_set(x_384, 2, x_13);
lean_ctor_set(x_384, 3, x_14);
lean_ctor_set(x_384, 4, x_15);
lean_ctor_set(x_384, 5, x_16);
lean_ctor_set(x_384, 6, x_17);
lean_ctor_set_uint64(x_384, sizeof(void*)*7, x_383);
lean_ctor_set_uint8(x_384, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_384, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_384, sizeof(void*)*7 + 10, x_265);
x_385 = 0;
x_386 = l_Lean_Meta_DiscrTree_mkPath(x_380, x_385, x_384, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_389 = x_386;
} else {
 lean_dec_ref(x_386);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_386, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_386, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_393 = x_386;
} else {
 lean_dec_ref(x_386);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint64_t x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; 
x_395 = l_Lean_Expr_appFn_x21(x_304);
lean_dec(x_304);
x_396 = l_Lean_Expr_appArg_x21(x_395);
lean_dec(x_395);
x_397 = l_Lean_Meta_simpGlobalConfig;
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get_uint64(x_397, sizeof(void*)*1);
if (lean_is_scalar(x_303)) {
 x_400 = lean_alloc_ctor(0, 7, 11);
} else {
 x_400 = x_303;
}
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_12);
lean_ctor_set(x_400, 2, x_13);
lean_ctor_set(x_400, 3, x_14);
lean_ctor_set(x_400, 4, x_15);
lean_ctor_set(x_400, 5, x_16);
lean_ctor_set(x_400, 6, x_17);
lean_ctor_set_uint64(x_400, sizeof(void*)*7, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 10, x_265);
x_401 = 0;
x_402 = l_Lean_Meta_DiscrTree_mkPath(x_396, x_401, x_400, x_4, x_5, x_6, x_305);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_405 = x_402;
} else {
 lean_dec_ref(x_402);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_402, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_402, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_409 = x_402;
} else {
 lean_dec_ref(x_402);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_411 = lean_ctor_get(x_298, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_298, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_413 = x_298;
} else {
 lean_dec_ref(x_298);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_415 = lean_ctor_get(x_293, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_293, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_417 = x_293;
} else {
 lean_dec_ref(x_293);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_11, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = l_Lean_Syntax_getId(x_1);
x_16 = l_Lean_LocalContext_findFromUserName_x3f(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_1, x_17, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_ConstantInfo_type(x_23);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = l_Lean_LocalDecl_type(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_10, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_DiscrTree_keysAsPattern(x_14, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_log___at_Lean_Elab_Term_exceptionToSorry___spec__2(x_17, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrTreeKeyCmd", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1;
x_2 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2;
x_3 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5;
x_8 = l_Lean_Elab_Command_liftTermElabM___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_Command_liftTermElabM___rarg(x_11, x_2, x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DiscrTreeKey", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDiscrTreeKeyCmd", 19, 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6;
x_3 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4;
x_4 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5;
x_5 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(x_10, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_DiscrTree_keysAsPattern(x_14, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_log___at_Lean_Elab_Term_exceptionToSorry___spec__2(x_17, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrTreeSimpKeyCmd", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1;
x_2 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2;
x_3 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5;
x_8 = l_Lean_Elab_Command_liftTermElabM___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Elab_Command_liftTermElabM___rarg(x_11, x_2, x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDiscrTreeSimpKeyCmd", 23, 23);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6;
x_3 = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_DiscrTreeKey(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1();
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1);
l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2 = _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__4);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__5);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1);
l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2 = _init_l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__2);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
