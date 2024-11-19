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
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*6);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 8);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 9);
x_19 = 2;
lean_ctor_set_uint8(x_9, 9, x_19);
x_20 = 2;
x_21 = lean_uint64_shift_right(x_10, x_20);
x_22 = lean_uint64_shift_left(x_21, x_20);
x_23 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1;
x_24 = lean_uint64_lor(x_22, x_23);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_15);
lean_ctor_set_uint64(x_25, sizeof(void*)*6, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*6 + 9, x_18);
x_26 = 1;
x_27 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_26, x_8, x_27, x_25, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Meta_whnfR(x_32, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
if (x_2 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 0;
x_37 = l_Lean_Meta_DiscrTree_mkPath(x_34, x_36, x_3, x_4, x_5, x_6, x_35);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_39 = lean_ctor_get(x_3, 5);
lean_dec(x_39);
x_40 = lean_ctor_get(x_3, 4);
lean_dec(x_40);
x_41 = lean_ctor_get(x_3, 3);
lean_dec(x_41);
x_42 = lean_ctor_get(x_3, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_3, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Expr_isAppOfArity(x_45, x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_51 = lean_unsigned_to_nat(2u);
x_52 = l_Lean_Expr_isAppOfArity(x_45, x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_54 = l_Lean_Expr_isAppOfArity(x_45, x_53, x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_56 = lean_unsigned_to_nat(1u);
x_57 = l_Lean_Expr_isAppOfArity(x_45, x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint64_t x_60; uint8_t x_61; lean_object* x_62; 
x_58 = l_Lean_Meta_simpGlobalConfig;
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_58, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_59);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_60);
x_61 = 0;
x_62 = l_Lean_Meta_DiscrTree_mkPath(x_45, x_61, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_72 = l_Lean_Expr_isAppOfArity(x_71, x_47, x_48);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint64_t x_75; uint8_t x_76; lean_object* x_77; 
x_73 = l_Lean_Meta_simpGlobalConfig;
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get_uint64(x_73, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_74);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_75);
x_76 = 0;
x_77 = l_Lean_Meta_DiscrTree_mkPath(x_71, x_76, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; uint8_t x_91; lean_object* x_92; 
x_86 = l_Lean_Expr_appFn_x21(x_71);
lean_dec(x_71);
x_87 = l_Lean_Expr_appArg_x21(x_86);
lean_dec(x_86);
x_88 = l_Lean_Meta_simpGlobalConfig;
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get_uint64(x_88, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_89);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_90);
x_91 = 0;
x_92 = l_Lean_Meta_DiscrTree_mkPath(x_87, x_91, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
return x_92;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_92);
if (x_97 == 0)
{
return x_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint64_t x_105; uint8_t x_106; lean_object* x_107; 
x_101 = l_Lean_Expr_appFn_x21(x_45);
lean_dec(x_45);
x_102 = l_Lean_Expr_appArg_x21(x_101);
lean_dec(x_101);
x_103 = l_Lean_Meta_simpGlobalConfig;
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint64(x_103, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_104);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_105);
x_106 = 0;
x_107 = l_Lean_Meta_DiscrTree_mkPath(x_102, x_106, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; uint8_t x_121; lean_object* x_122; 
x_116 = l_Lean_Expr_appFn_x21(x_45);
lean_dec(x_45);
x_117 = l_Lean_Expr_appArg_x21(x_116);
lean_dec(x_116);
x_118 = l_Lean_Meta_simpGlobalConfig;
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get_uint64(x_118, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_119);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_120);
x_121 = 0;
x_122 = l_Lean_Meta_DiscrTree_mkPath(x_117, x_121, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
return x_122;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_122);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_122);
if (x_127 == 0)
{
return x_122;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint64_t x_135; uint8_t x_136; lean_object* x_137; 
x_131 = l_Lean_Expr_appFn_x21(x_45);
lean_dec(x_45);
x_132 = l_Lean_Expr_appArg_x21(x_131);
lean_dec(x_131);
x_133 = l_Lean_Meta_simpGlobalConfig;
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get_uint64(x_133, sizeof(void*)*1);
lean_ctor_set(x_3, 0, x_134);
lean_ctor_set_uint64(x_3, sizeof(void*)*6, x_135);
x_136 = 0;
x_137 = l_Lean_Meta_DiscrTree_mkPath(x_132, x_136, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_137);
if (x_142 == 0)
{
return x_137;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_137, 0);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_137);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
lean_dec(x_3);
x_146 = lean_ctor_get(x_33, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_33, 1);
lean_inc(x_147);
lean_dec(x_33);
x_148 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_149 = lean_unsigned_to_nat(3u);
x_150 = l_Lean_Expr_isAppOfArity(x_146, x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_152 = lean_unsigned_to_nat(2u);
x_153 = l_Lean_Expr_isAppOfArity(x_146, x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_155 = l_Lean_Expr_isAppOfArity(x_146, x_154, x_149);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_157 = lean_unsigned_to_nat(1u);
x_158 = l_Lean_Expr_isAppOfArity(x_146, x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint64_t x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_159 = l_Lean_Meta_simpGlobalConfig;
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get_uint64(x_159, sizeof(void*)*1);
x_162 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_11);
lean_ctor_set(x_162, 2, x_12);
lean_ctor_set(x_162, 3, x_13);
lean_ctor_set(x_162, 4, x_14);
lean_ctor_set(x_162, 5, x_15);
lean_ctor_set_uint64(x_162, sizeof(void*)*6, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_162, sizeof(void*)*6 + 9, x_18);
x_163 = 0;
x_164 = l_Lean_Meta_DiscrTree_mkPath(x_146, x_163, x_162, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_171 = x_164;
} else {
 lean_dec_ref(x_164);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = l_Lean_Expr_appArg_x21(x_146);
lean_dec(x_146);
x_174 = l_Lean_Expr_isAppOfArity(x_173, x_148, x_149);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint64_t x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_175 = l_Lean_Meta_simpGlobalConfig;
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get_uint64(x_175, sizeof(void*)*1);
x_178 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 2, x_12);
lean_ctor_set(x_178, 3, x_13);
lean_ctor_set(x_178, 4, x_14);
lean_ctor_set(x_178, 5, x_15);
lean_ctor_set_uint64(x_178, sizeof(void*)*6, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_178, sizeof(void*)*6 + 9, x_18);
x_179 = 0;
x_180 = l_Lean_Meta_DiscrTree_mkPath(x_173, x_179, x_178, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_180, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_187 = x_180;
} else {
 lean_dec_ref(x_180);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint64_t x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_189 = l_Lean_Expr_appFn_x21(x_173);
lean_dec(x_173);
x_190 = l_Lean_Expr_appArg_x21(x_189);
lean_dec(x_189);
x_191 = l_Lean_Meta_simpGlobalConfig;
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get_uint64(x_191, sizeof(void*)*1);
x_194 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_11);
lean_ctor_set(x_194, 2, x_12);
lean_ctor_set(x_194, 3, x_13);
lean_ctor_set(x_194, 4, x_14);
lean_ctor_set(x_194, 5, x_15);
lean_ctor_set_uint64(x_194, sizeof(void*)*6, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_194, sizeof(void*)*6 + 9, x_18);
x_195 = 0;
x_196 = l_Lean_Meta_DiscrTree_mkPath(x_190, x_195, x_194, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_196, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_203 = x_196;
} else {
 lean_dec_ref(x_196);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint64_t x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_205 = l_Lean_Expr_appFn_x21(x_146);
lean_dec(x_146);
x_206 = l_Lean_Expr_appArg_x21(x_205);
lean_dec(x_205);
x_207 = l_Lean_Meta_simpGlobalConfig;
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get_uint64(x_207, sizeof(void*)*1);
x_210 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_11);
lean_ctor_set(x_210, 2, x_12);
lean_ctor_set(x_210, 3, x_13);
lean_ctor_set(x_210, 4, x_14);
lean_ctor_set(x_210, 5, x_15);
lean_ctor_set_uint64(x_210, sizeof(void*)*6, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_210, sizeof(void*)*6 + 9, x_18);
x_211 = 0;
x_212 = l_Lean_Meta_DiscrTree_mkPath(x_206, x_211, x_210, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_219 = x_212;
} else {
 lean_dec_ref(x_212);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint64_t x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; 
x_221 = l_Lean_Expr_appFn_x21(x_146);
lean_dec(x_146);
x_222 = l_Lean_Expr_appArg_x21(x_221);
lean_dec(x_221);
x_223 = l_Lean_Meta_simpGlobalConfig;
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get_uint64(x_223, sizeof(void*)*1);
x_226 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_11);
lean_ctor_set(x_226, 2, x_12);
lean_ctor_set(x_226, 3, x_13);
lean_ctor_set(x_226, 4, x_14);
lean_ctor_set(x_226, 5, x_15);
lean_ctor_set_uint64(x_226, sizeof(void*)*6, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_226, sizeof(void*)*6 + 9, x_18);
x_227 = 0;
x_228 = l_Lean_Meta_DiscrTree_mkPath(x_222, x_227, x_226, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_228, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_235 = x_228;
} else {
 lean_dec_ref(x_228);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint64_t x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; 
x_237 = l_Lean_Expr_appFn_x21(x_146);
lean_dec(x_146);
x_238 = l_Lean_Expr_appArg_x21(x_237);
lean_dec(x_237);
x_239 = l_Lean_Meta_simpGlobalConfig;
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get_uint64(x_239, sizeof(void*)*1);
x_242 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_11);
lean_ctor_set(x_242, 2, x_12);
lean_ctor_set(x_242, 3, x_13);
lean_ctor_set(x_242, 4, x_14);
lean_ctor_set(x_242, 5, x_15);
lean_ctor_set_uint64(x_242, sizeof(void*)*6, x_241);
lean_ctor_set_uint8(x_242, sizeof(void*)*6 + 8, x_17);
lean_ctor_set_uint8(x_242, sizeof(void*)*6 + 9, x_18);
x_243 = 0;
x_244 = l_Lean_Meta_DiscrTree_mkPath(x_238, x_243, x_242, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_33);
if (x_253 == 0)
{
return x_33;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_33, 0);
x_255 = lean_ctor_get(x_33, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_33);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_257 = !lean_is_exclusive(x_28);
if (x_257 == 0)
{
return x_28;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_28, 0);
x_259 = lean_ctor_get(x_28, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_28);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; uint8_t x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; lean_object* x_281; uint64_t x_282; uint64_t x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; lean_object* x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; 
x_261 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 8);
x_262 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 9);
x_263 = lean_ctor_get_uint8(x_9, 0);
x_264 = lean_ctor_get_uint8(x_9, 1);
x_265 = lean_ctor_get_uint8(x_9, 2);
x_266 = lean_ctor_get_uint8(x_9, 3);
x_267 = lean_ctor_get_uint8(x_9, 4);
x_268 = lean_ctor_get_uint8(x_9, 5);
x_269 = lean_ctor_get_uint8(x_9, 6);
x_270 = lean_ctor_get_uint8(x_9, 7);
x_271 = lean_ctor_get_uint8(x_9, 8);
x_272 = lean_ctor_get_uint8(x_9, 10);
x_273 = lean_ctor_get_uint8(x_9, 11);
x_274 = lean_ctor_get_uint8(x_9, 12);
x_275 = lean_ctor_get_uint8(x_9, 13);
x_276 = lean_ctor_get_uint8(x_9, 14);
x_277 = lean_ctor_get_uint8(x_9, 15);
x_278 = lean_ctor_get_uint8(x_9, 16);
x_279 = lean_ctor_get_uint8(x_9, 17);
lean_dec(x_9);
x_280 = 2;
x_281 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_281, 0, x_263);
lean_ctor_set_uint8(x_281, 1, x_264);
lean_ctor_set_uint8(x_281, 2, x_265);
lean_ctor_set_uint8(x_281, 3, x_266);
lean_ctor_set_uint8(x_281, 4, x_267);
lean_ctor_set_uint8(x_281, 5, x_268);
lean_ctor_set_uint8(x_281, 6, x_269);
lean_ctor_set_uint8(x_281, 7, x_270);
lean_ctor_set_uint8(x_281, 8, x_271);
lean_ctor_set_uint8(x_281, 9, x_280);
lean_ctor_set_uint8(x_281, 10, x_272);
lean_ctor_set_uint8(x_281, 11, x_273);
lean_ctor_set_uint8(x_281, 12, x_274);
lean_ctor_set_uint8(x_281, 13, x_275);
lean_ctor_set_uint8(x_281, 14, x_276);
lean_ctor_set_uint8(x_281, 15, x_277);
lean_ctor_set_uint8(x_281, 16, x_278);
lean_ctor_set_uint8(x_281, 17, x_279);
x_282 = 2;
x_283 = lean_uint64_shift_right(x_10, x_282);
x_284 = lean_uint64_shift_left(x_283, x_282);
x_285 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1;
x_286 = lean_uint64_lor(x_284, x_285);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_287 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_287, 0, x_281);
lean_ctor_set(x_287, 1, x_11);
lean_ctor_set(x_287, 2, x_12);
lean_ctor_set(x_287, 3, x_13);
lean_ctor_set(x_287, 4, x_14);
lean_ctor_set(x_287, 5, x_15);
lean_ctor_set_uint64(x_287, sizeof(void*)*6, x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_287, sizeof(void*)*6 + 9, x_262);
x_288 = 1;
x_289 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_290 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_288, x_8, x_289, x_287, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_dec(x_290);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_295 = l_Lean_Meta_whnfR(x_294, x_3, x_4, x_5, x_6, x_293);
if (lean_obj_tag(x_295) == 0)
{
if (x_2 == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = 0;
x_299 = l_Lean_Meta_DiscrTree_mkPath(x_296, x_298, x_3, x_4, x_5, x_6, x_297);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_300 = x_3;
} else {
 lean_dec_ref(x_3);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_295, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_295, 1);
lean_inc(x_302);
lean_dec(x_295);
x_303 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3;
x_304 = lean_unsigned_to_nat(3u);
x_305 = l_Lean_Expr_isAppOfArity(x_301, x_303, x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5;
x_307 = lean_unsigned_to_nat(2u);
x_308 = l_Lean_Expr_isAppOfArity(x_301, x_306, x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7;
x_310 = l_Lean_Expr_isAppOfArity(x_301, x_309, x_304);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__9;
x_312 = lean_unsigned_to_nat(1u);
x_313 = l_Lean_Expr_isAppOfArity(x_301, x_311, x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint64_t x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_314 = l_Lean_Meta_simpGlobalConfig;
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get_uint64(x_314, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_317 = lean_alloc_ctor(0, 6, 10);
} else {
 x_317 = x_300;
}
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_11);
lean_ctor_set(x_317, 2, x_12);
lean_ctor_set(x_317, 3, x_13);
lean_ctor_set(x_317, 4, x_14);
lean_ctor_set(x_317, 5, x_15);
lean_ctor_set_uint64(x_317, sizeof(void*)*6, x_316);
lean_ctor_set_uint8(x_317, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_317, sizeof(void*)*6 + 9, x_262);
x_318 = 0;
x_319 = l_Lean_Meta_DiscrTree_mkPath(x_301, x_318, x_317, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_319, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_326 = x_319;
} else {
 lean_dec_ref(x_319);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; uint8_t x_329; 
x_328 = l_Lean_Expr_appArg_x21(x_301);
lean_dec(x_301);
x_329 = l_Lean_Expr_isAppOfArity(x_328, x_303, x_304);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; uint64_t x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_330 = l_Lean_Meta_simpGlobalConfig;
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get_uint64(x_330, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_333 = lean_alloc_ctor(0, 6, 10);
} else {
 x_333 = x_300;
}
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_11);
lean_ctor_set(x_333, 2, x_12);
lean_ctor_set(x_333, 3, x_13);
lean_ctor_set(x_333, 4, x_14);
lean_ctor_set(x_333, 5, x_15);
lean_ctor_set_uint64(x_333, sizeof(void*)*6, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_333, sizeof(void*)*6 + 9, x_262);
x_334 = 0;
x_335 = l_Lean_Meta_DiscrTree_mkPath(x_328, x_334, x_333, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_335, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_335, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_342 = x_335;
} else {
 lean_dec_ref(x_335);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint64_t x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; 
x_344 = l_Lean_Expr_appFn_x21(x_328);
lean_dec(x_328);
x_345 = l_Lean_Expr_appArg_x21(x_344);
lean_dec(x_344);
x_346 = l_Lean_Meta_simpGlobalConfig;
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get_uint64(x_346, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_349 = lean_alloc_ctor(0, 6, 10);
} else {
 x_349 = x_300;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_11);
lean_ctor_set(x_349, 2, x_12);
lean_ctor_set(x_349, 3, x_13);
lean_ctor_set(x_349, 4, x_14);
lean_ctor_set(x_349, 5, x_15);
lean_ctor_set_uint64(x_349, sizeof(void*)*6, x_348);
lean_ctor_set_uint8(x_349, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_349, sizeof(void*)*6 + 9, x_262);
x_350 = 0;
x_351 = l_Lean_Meta_DiscrTree_mkPath(x_345, x_350, x_349, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_351, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_351, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_358 = x_351;
} else {
 lean_dec_ref(x_351);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint64_t x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; 
x_360 = l_Lean_Expr_appFn_x21(x_301);
lean_dec(x_301);
x_361 = l_Lean_Expr_appArg_x21(x_360);
lean_dec(x_360);
x_362 = l_Lean_Meta_simpGlobalConfig;
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint64(x_362, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_365 = lean_alloc_ctor(0, 6, 10);
} else {
 x_365 = x_300;
}
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_11);
lean_ctor_set(x_365, 2, x_12);
lean_ctor_set(x_365, 3, x_13);
lean_ctor_set(x_365, 4, x_14);
lean_ctor_set(x_365, 5, x_15);
lean_ctor_set_uint64(x_365, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_365, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_365, sizeof(void*)*6 + 9, x_262);
x_366 = 0;
x_367 = l_Lean_Meta_DiscrTree_mkPath(x_361, x_366, x_365, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_367, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_374 = x_367;
} else {
 lean_dec_ref(x_367);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint64_t x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; 
x_376 = l_Lean_Expr_appFn_x21(x_301);
lean_dec(x_301);
x_377 = l_Lean_Expr_appArg_x21(x_376);
lean_dec(x_376);
x_378 = l_Lean_Meta_simpGlobalConfig;
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get_uint64(x_378, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_381 = lean_alloc_ctor(0, 6, 10);
} else {
 x_381 = x_300;
}
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 2, x_12);
lean_ctor_set(x_381, 3, x_13);
lean_ctor_set(x_381, 4, x_14);
lean_ctor_set(x_381, 5, x_15);
lean_ctor_set_uint64(x_381, sizeof(void*)*6, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_381, sizeof(void*)*6 + 9, x_262);
x_382 = 0;
x_383 = l_Lean_Meta_DiscrTree_mkPath(x_377, x_382, x_381, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_388 = lean_ctor_get(x_383, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_383, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_390 = x_383;
} else {
 lean_dec_ref(x_383);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint64_t x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_392 = l_Lean_Expr_appFn_x21(x_301);
lean_dec(x_301);
x_393 = l_Lean_Expr_appArg_x21(x_392);
lean_dec(x_392);
x_394 = l_Lean_Meta_simpGlobalConfig;
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get_uint64(x_394, sizeof(void*)*1);
if (lean_is_scalar(x_300)) {
 x_397 = lean_alloc_ctor(0, 6, 10);
} else {
 x_397 = x_300;
}
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_11);
lean_ctor_set(x_397, 2, x_12);
lean_ctor_set(x_397, 3, x_13);
lean_ctor_set(x_397, 4, x_14);
lean_ctor_set(x_397, 5, x_15);
lean_ctor_set_uint64(x_397, sizeof(void*)*6, x_396);
lean_ctor_set_uint8(x_397, sizeof(void*)*6 + 8, x_261);
lean_ctor_set_uint8(x_397, sizeof(void*)*6 + 9, x_262);
x_398 = 0;
x_399 = l_Lean_Meta_DiscrTree_mkPath(x_393, x_398, x_397, x_4, x_5, x_6, x_302);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_404 = lean_ctor_get(x_399, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_399, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_406 = x_399;
} else {
 lean_dec_ref(x_399);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_408 = lean_ctor_get(x_295, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_295, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_410 = x_295;
} else {
 lean_dec_ref(x_295);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_412 = lean_ctor_get(x_290, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_290, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_414 = x_290;
} else {
 lean_dec_ref(x_290);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_413);
return x_415;
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
x_14 = lean_ctor_get(x_4, 1);
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
