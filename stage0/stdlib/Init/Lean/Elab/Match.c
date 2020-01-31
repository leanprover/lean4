// Lean compiler output
// Module: Init.Lean.Elab.Match
// Imports: Init.Lean.Elab.Term
#include "runtime/lean.h"
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
lean_object* l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch(lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
extern uint8_t l_Lean_Elab_Term_elabParen___closed__4;
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_let___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_8 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Term_getMainModule___rarg(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Array_empty___closed__1;
x_13 = lean_array_push(x_12, x_3);
x_14 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_array_push(x_15, x_14);
x_17 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_array_push(x_25, x_4);
x_27 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_6, 8);
lean_inc(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_6, 8, x_32);
x_33 = 1;
x_34 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_33, x_28, x_6, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_ctor_get(x_6, 3);
x_39 = lean_ctor_get(x_6, 4);
x_40 = lean_ctor_get(x_6, 5);
x_41 = lean_ctor_get(x_6, 6);
x_42 = lean_ctor_get(x_6, 7);
x_43 = lean_ctor_get(x_6, 8);
x_44 = lean_ctor_get(x_6, 9);
x_45 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_47 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
lean_inc(x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_37);
lean_ctor_set(x_50, 3, x_38);
lean_ctor_set(x_50, 4, x_39);
lean_ctor_set(x_50, 5, x_40);
lean_ctor_set(x_50, 6, x_41);
lean_ctor_set(x_50, 7, x_42);
lean_ctor_set(x_50, 8, x_49);
lean_ctor_set(x_50, 9, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 1, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 2, x_47);
x_51 = 1;
x_52 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_51, x_28, x_50, x_11);
return x_52;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_9 = l_Lean_Elab_Term_getCurrMacroScope(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Term_getMainModule___rarg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Array_empty___closed__1;
x_14 = lean_array_push(x_13, x_3);
x_15 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_16 = lean_array_push(x_14, x_15);
x_17 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
x_18 = lean_array_push(x_17, x_4);
x_19 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_13, x_20);
x_22 = l_Lean_nullKind___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_array_push(x_16, x_23);
x_25 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_array_push(x_26, x_2);
x_28 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_array_push(x_33, x_5);
x_35 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_7, 8);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_7, 8, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_41, x_36, x_7, x_12);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
x_45 = lean_ctor_get(x_7, 2);
x_46 = lean_ctor_get(x_7, 3);
x_47 = lean_ctor_get(x_7, 4);
x_48 = lean_ctor_get(x_7, 5);
x_49 = lean_ctor_get(x_7, 6);
x_50 = lean_ctor_get(x_7, 7);
x_51 = lean_ctor_get(x_7, 8);
x_52 = lean_ctor_get(x_7, 9);
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
x_55 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
lean_inc(x_36);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
x_58 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_44);
lean_ctor_set(x_58, 2, x_45);
lean_ctor_set(x_58, 3, x_46);
lean_ctor_set(x_58, 4, x_47);
lean_ctor_set(x_58, 5, x_48);
lean_ctor_set(x_58, 6, x_49);
lean_ctor_set(x_58, 7, x_50);
lean_ctor_set(x_58, 8, x_57);
lean_ctor_set(x_58, 9, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_55);
x_59 = 1;
x_60 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_59, x_36, x_58, x_12);
return x_60;
}
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_342; uint8_t x_343; 
x_342 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_inc(x_1);
x_343 = l_Lean_Syntax_isOfKind(x_1, x_342);
if (x_343 == 0)
{
uint8_t x_344; 
x_344 = 0;
x_5 = x_344;
goto block_341;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = l_Lean_Syntax_getArgs(x_1);
x_346 = lean_array_get_size(x_345);
lean_dec(x_345);
x_347 = lean_unsigned_to_nat(6u);
x_348 = lean_nat_dec_eq(x_346, x_347);
lean_dec(x_346);
x_5 = x_348;
goto block_341;
}
block_341:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_335; uint8_t x_336; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_335 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_336 = l_Lean_Syntax_isOfKind(x_9, x_335);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = 0;
x_10 = x_337;
goto block_334;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = l_Lean_Syntax_getArgs(x_9);
x_339 = lean_array_get_size(x_338);
lean_dec(x_338);
x_340 = lean_nat_dec_eq(x_339, x_8);
lean_dec(x_339);
x_10 = x_340;
goto block_334;
}
block_334:
{
uint8_t x_11; 
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_179; uint8_t x_180; uint8_t x_181; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
lean_dec(x_9);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_179 = l_Lean_nullKind___closed__2;
lean_inc(x_16);
x_180 = l_Lean_Syntax_isOfKind(x_16, x_179);
if (x_180 == 0)
{
uint8_t x_330; 
x_330 = 0;
x_181 = x_330;
goto block_329;
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = l_Lean_Syntax_getArgs(x_16);
x_332 = lean_array_get_size(x_331);
lean_dec(x_331);
x_333 = lean_nat_dec_eq(x_332, x_13);
lean_dec(x_332);
x_181 = x_333;
goto block_329;
}
block_178:
{
uint8_t x_18; 
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_172; uint8_t x_173; 
x_20 = l_Lean_Syntax_getArg(x_16, x_13);
lean_dec(x_16);
x_172 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_20);
x_173 = l_Lean_Syntax_isOfKind(x_20, x_172);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = 0;
x_21 = x_174;
goto block_171;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = l_Lean_Syntax_getArgs(x_20);
x_176 = lean_array_get_size(x_175);
lean_dec(x_175);
x_177 = lean_nat_dec_eq(x_176, x_15);
lean_dec(x_176);
x_21 = x_177;
goto block_171;
}
block_171:
{
uint8_t x_22; 
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_96; uint8_t x_97; uint8_t x_98; 
x_24 = l_Lean_Syntax_getArg(x_20, x_8);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(4u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_96 = l_Lean_nullKind___closed__2;
lean_inc(x_26);
x_97 = l_Lean_Syntax_isOfKind(x_26, x_96);
if (x_97 == 0)
{
uint8_t x_167; 
x_167 = 0;
x_98 = x_167;
goto block_166;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = l_Lean_Syntax_getArgs(x_26);
x_169 = lean_array_get_size(x_168);
lean_dec(x_168);
x_170 = lean_nat_dec_eq(x_169, x_13);
lean_dec(x_169);
x_98 = x_170;
goto block_166;
}
block_95:
{
uint8_t x_28; 
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_89; uint8_t x_90; 
x_30 = lean_unsigned_to_nat(5u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
x_89 = l_Lean_nullKind___closed__2;
lean_inc(x_31);
x_90 = l_Lean_Syntax_isOfKind(x_31, x_89);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_32 = x_91;
goto block_88;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = l_Lean_Syntax_getArgs(x_31);
x_93 = lean_array_get_size(x_92);
lean_dec(x_92);
x_94 = lean_nat_dec_eq(x_93, x_8);
lean_dec(x_93);
x_32 = x_94;
goto block_88;
}
block_88:
{
uint8_t x_33; 
x_33 = l_coeDecidableEq(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_81; uint8_t x_82; 
x_35 = l_Lean_Syntax_getArg(x_31, x_13);
lean_dec(x_31);
x_81 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_35);
x_82 = l_Lean_Syntax_isOfKind(x_35, x_81);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = 0;
x_36 = x_83;
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = l_Lean_Syntax_getArgs(x_35);
x_85 = lean_array_get_size(x_84);
lean_dec(x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_dec_eq(x_85, x_86);
lean_dec(x_85);
x_36 = x_87;
goto block_80;
}
block_80:
{
uint8_t x_37; 
x_37 = l_coeDecidableEq(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_74; uint8_t x_75; 
x_39 = l_Lean_Syntax_getArg(x_35, x_13);
x_74 = l_Lean_nullKind___closed__2;
lean_inc(x_39);
x_75 = l_Lean_Syntax_isOfKind(x_39, x_74);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = 0;
x_40 = x_76;
goto block_73;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = l_Lean_Syntax_getArgs(x_39);
x_78 = lean_array_get_size(x_77);
lean_dec(x_77);
x_79 = lean_nat_dec_eq(x_78, x_8);
lean_dec(x_78);
x_40 = x_79;
goto block_73;
}
block_73:
{
uint8_t x_41; 
x_41 = l_coeDecidableEq(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_67; uint8_t x_68; 
x_43 = l_Lean_Syntax_getArg(x_39, x_13);
lean_dec(x_39);
x_67 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_43);
x_68 = l_Lean_Syntax_isOfKind(x_43, x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_44 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Syntax_getArgs(x_43);
x_71 = lean_array_get_size(x_70);
lean_dec(x_70);
x_72 = lean_nat_dec_eq(x_71, x_15);
lean_dec(x_71);
x_44 = x_72;
goto block_66;
}
block_66:
{
uint8_t x_45; 
x_45 = l_coeDecidableEq(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = l_Lean_Syntax_getArg(x_43, x_13);
x_48 = l_Lean_identKind___closed__2;
lean_inc(x_47);
x_49 = l_Lean_Syntax_isOfKind(x_47, x_48);
x_50 = l_coeDecidableEq(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Syntax_getArg(x_43, x_8);
lean_dec(x_43);
x_53 = l_Lean_nullKind___closed__2;
lean_inc(x_52);
x_54 = l_Lean_Syntax_isOfKind(x_52, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_elabParen___closed__4;
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_47);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Syntax_getArg(x_35, x_15);
lean_dec(x_35);
x_58 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_14, x_47, x_24, x_57, x_2, x_3, x_4);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_59 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_60 = lean_array_get_size(x_59);
lean_dec(x_59);
x_61 = lean_nat_dec_eq(x_60, x_13);
lean_dec(x_60);
x_62 = l_coeDecidableEq(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_47);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Syntax_getArg(x_35, x_15);
lean_dec(x_35);
x_65 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_14, x_47, x_24, x_64, x_2, x_3, x_4);
return x_65;
}
}
}
}
}
}
}
}
}
}
}
}
}
block_166:
{
uint8_t x_99; 
x_99 = l_coeDecidableEq(x_98);
if (x_99 == 0)
{
if (x_97 == 0)
{
uint8_t x_100; 
lean_dec(x_26);
x_100 = 0;
x_27 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_Syntax_getArgs(x_26);
lean_dec(x_26);
x_102 = lean_array_get_size(x_101);
lean_dec(x_101);
x_103 = lean_nat_dec_eq(x_102, x_8);
lean_dec(x_102);
x_27 = x_103;
goto block_95;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_161; 
lean_dec(x_26);
x_104 = lean_unsigned_to_nat(5u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_inc(x_105);
x_161 = l_Lean_Syntax_isOfKind(x_105, x_96);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = 0;
x_106 = x_162;
goto block_160;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = l_Lean_Syntax_getArgs(x_105);
x_164 = lean_array_get_size(x_163);
lean_dec(x_163);
x_165 = lean_nat_dec_eq(x_164, x_8);
lean_dec(x_164);
x_106 = x_165;
goto block_160;
}
block_160:
{
uint8_t x_107; 
x_107 = l_coeDecidableEq(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_153; uint8_t x_154; 
x_109 = l_Lean_Syntax_getArg(x_105, x_13);
lean_dec(x_105);
x_153 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_109);
x_154 = l_Lean_Syntax_isOfKind(x_109, x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = 0;
x_110 = x_155;
goto block_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = l_Lean_Syntax_getArgs(x_109);
x_157 = lean_array_get_size(x_156);
lean_dec(x_156);
x_158 = lean_unsigned_to_nat(3u);
x_159 = lean_nat_dec_eq(x_157, x_158);
lean_dec(x_157);
x_110 = x_159;
goto block_152;
}
block_152:
{
uint8_t x_111; 
x_111 = l_coeDecidableEq(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_112;
}
else
{
lean_object* x_113; uint8_t x_114; uint8_t x_147; 
x_113 = l_Lean_Syntax_getArg(x_109, x_13);
lean_inc(x_113);
x_147 = l_Lean_Syntax_isOfKind(x_113, x_96);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = 0;
x_114 = x_148;
goto block_146;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_Syntax_getArgs(x_113);
x_150 = lean_array_get_size(x_149);
lean_dec(x_149);
x_151 = lean_nat_dec_eq(x_150, x_8);
lean_dec(x_150);
x_114 = x_151;
goto block_146;
}
block_146:
{
uint8_t x_115; 
x_115 = l_coeDecidableEq(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_140; uint8_t x_141; 
x_117 = l_Lean_Syntax_getArg(x_113, x_13);
lean_dec(x_113);
x_140 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_117);
x_141 = l_Lean_Syntax_isOfKind(x_117, x_140);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = 0;
x_118 = x_142;
goto block_139;
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = l_Lean_Syntax_getArgs(x_117);
x_144 = lean_array_get_size(x_143);
lean_dec(x_143);
x_145 = lean_nat_dec_eq(x_144, x_15);
lean_dec(x_144);
x_118 = x_145;
goto block_139;
}
block_139:
{
uint8_t x_119; 
x_119 = l_coeDecidableEq(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_117);
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; 
x_121 = l_Lean_Syntax_getArg(x_117, x_13);
x_122 = l_Lean_identKind___closed__2;
lean_inc(x_121);
x_123 = l_Lean_Syntax_isOfKind(x_121, x_122);
x_124 = l_coeDecidableEq(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_125;
}
else
{
lean_object* x_126; uint8_t x_127; 
x_126 = l_Lean_Syntax_getArg(x_117, x_8);
lean_dec(x_117);
lean_inc(x_126);
x_127 = l_Lean_Syntax_isOfKind(x_126, x_96);
if (x_127 == 0)
{
uint8_t x_128; 
lean_dec(x_126);
x_128 = l_Lean_Elab_Term_elabParen___closed__4;
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_121);
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = l_Lean_Syntax_getArg(x_109, x_15);
lean_dec(x_109);
x_131 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_14, x_121, x_24, x_130, x_2, x_3, x_4);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; 
x_132 = l_Lean_Syntax_getArgs(x_126);
lean_dec(x_126);
x_133 = lean_array_get_size(x_132);
lean_dec(x_132);
x_134 = lean_nat_dec_eq(x_133, x_13);
lean_dec(x_133);
x_135 = l_coeDecidableEq(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_121);
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Lean_Syntax_getArg(x_109, x_15);
lean_dec(x_109);
x_138 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_14, x_121, x_24, x_137, x_2, x_3, x_4);
return x_138;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
block_329:
{
uint8_t x_182; 
x_182 = l_coeDecidableEq(x_181);
if (x_182 == 0)
{
if (x_180 == 0)
{
uint8_t x_183; 
x_183 = 0;
x_17 = x_183;
goto block_178;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = l_Lean_Syntax_getArgs(x_16);
x_185 = lean_array_get_size(x_184);
lean_dec(x_184);
x_186 = lean_nat_dec_eq(x_185, x_8);
lean_dec(x_185);
x_17 = x_186;
goto block_178;
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_255; uint8_t x_256; 
lean_dec(x_16);
x_187 = lean_unsigned_to_nat(4u);
x_188 = l_Lean_Syntax_getArg(x_1, x_187);
lean_inc(x_188);
x_255 = l_Lean_Syntax_isOfKind(x_188, x_179);
if (x_255 == 0)
{
uint8_t x_325; 
x_325 = 0;
x_256 = x_325;
goto block_324;
}
else
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_326 = l_Lean_Syntax_getArgs(x_188);
x_327 = lean_array_get_size(x_326);
lean_dec(x_326);
x_328 = lean_nat_dec_eq(x_327, x_13);
lean_dec(x_327);
x_256 = x_328;
goto block_324;
}
block_254:
{
uint8_t x_190; 
x_190 = l_coeDecidableEq(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_249; 
x_192 = lean_unsigned_to_nat(5u);
x_193 = l_Lean_Syntax_getArg(x_1, x_192);
lean_inc(x_193);
x_249 = l_Lean_Syntax_isOfKind(x_193, x_179);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = 0;
x_194 = x_250;
goto block_248;
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = l_Lean_Syntax_getArgs(x_193);
x_252 = lean_array_get_size(x_251);
lean_dec(x_251);
x_253 = lean_nat_dec_eq(x_252, x_8);
lean_dec(x_252);
x_194 = x_253;
goto block_248;
}
block_248:
{
uint8_t x_195; 
x_195 = l_coeDecidableEq(x_194);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_196;
}
else
{
lean_object* x_197; uint8_t x_198; lean_object* x_241; uint8_t x_242; 
x_197 = l_Lean_Syntax_getArg(x_193, x_13);
lean_dec(x_193);
x_241 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_197);
x_242 = l_Lean_Syntax_isOfKind(x_197, x_241);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = 0;
x_198 = x_243;
goto block_240;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = l_Lean_Syntax_getArgs(x_197);
x_245 = lean_array_get_size(x_244);
lean_dec(x_244);
x_246 = lean_unsigned_to_nat(3u);
x_247 = lean_nat_dec_eq(x_245, x_246);
lean_dec(x_245);
x_198 = x_247;
goto block_240;
}
block_240:
{
uint8_t x_199; 
x_199 = l_coeDecidableEq(x_198);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_200;
}
else
{
lean_object* x_201; uint8_t x_202; uint8_t x_235; 
x_201 = l_Lean_Syntax_getArg(x_197, x_13);
lean_inc(x_201);
x_235 = l_Lean_Syntax_isOfKind(x_201, x_179);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = 0;
x_202 = x_236;
goto block_234;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_237 = l_Lean_Syntax_getArgs(x_201);
x_238 = lean_array_get_size(x_237);
lean_dec(x_237);
x_239 = lean_nat_dec_eq(x_238, x_8);
lean_dec(x_238);
x_202 = x_239;
goto block_234;
}
block_234:
{
uint8_t x_203; 
x_203 = l_coeDecidableEq(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_204;
}
else
{
lean_object* x_205; uint8_t x_206; lean_object* x_228; uint8_t x_229; 
x_205 = l_Lean_Syntax_getArg(x_201, x_13);
lean_dec(x_201);
x_228 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_205);
x_229 = l_Lean_Syntax_isOfKind(x_205, x_228);
if (x_229 == 0)
{
uint8_t x_230; 
x_230 = 0;
x_206 = x_230;
goto block_227;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = l_Lean_Syntax_getArgs(x_205);
x_232 = lean_array_get_size(x_231);
lean_dec(x_231);
x_233 = lean_nat_dec_eq(x_232, x_15);
lean_dec(x_232);
x_206 = x_233;
goto block_227;
}
block_227:
{
uint8_t x_207; 
x_207 = l_coeDecidableEq(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
lean_dec(x_205);
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_208 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; 
x_209 = l_Lean_Syntax_getArg(x_205, x_13);
x_210 = l_Lean_identKind___closed__2;
lean_inc(x_209);
x_211 = l_Lean_Syntax_isOfKind(x_209, x_210);
x_212 = l_coeDecidableEq(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_205);
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_213;
}
else
{
lean_object* x_214; uint8_t x_215; 
x_214 = l_Lean_Syntax_getArg(x_205, x_8);
lean_dec(x_205);
lean_inc(x_214);
x_215 = l_Lean_Syntax_isOfKind(x_214, x_179);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_214);
x_216 = l_Lean_Elab_Term_elabParen___closed__4;
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_209);
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = l_Lean_Syntax_getArg(x_197, x_15);
lean_dec(x_197);
x_219 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_14, x_209, x_218, x_2, x_3, x_4);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; 
x_220 = l_Lean_Syntax_getArgs(x_214);
lean_dec(x_214);
x_221 = lean_array_get_size(x_220);
lean_dec(x_220);
x_222 = lean_nat_dec_eq(x_221, x_13);
lean_dec(x_221);
x_223 = l_coeDecidableEq(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_209);
lean_dec(x_197);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = l_Lean_Syntax_getArg(x_197, x_15);
lean_dec(x_197);
x_226 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_14, x_209, x_225, x_2, x_3, x_4);
return x_226;
}
}
}
}
}
}
}
}
}
}
}
}
}
block_324:
{
uint8_t x_257; 
x_257 = l_coeDecidableEq(x_256);
if (x_257 == 0)
{
if (x_255 == 0)
{
uint8_t x_258; 
lean_dec(x_188);
x_258 = 0;
x_189 = x_258;
goto block_254;
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = l_Lean_Syntax_getArgs(x_188);
lean_dec(x_188);
x_260 = lean_array_get_size(x_259);
lean_dec(x_259);
x_261 = lean_nat_dec_eq(x_260, x_8);
lean_dec(x_260);
x_189 = x_261;
goto block_254;
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_319; 
lean_dec(x_188);
x_262 = lean_unsigned_to_nat(5u);
x_263 = l_Lean_Syntax_getArg(x_1, x_262);
lean_inc(x_263);
x_319 = l_Lean_Syntax_isOfKind(x_263, x_179);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = 0;
x_264 = x_320;
goto block_318;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = l_Lean_Syntax_getArgs(x_263);
x_322 = lean_array_get_size(x_321);
lean_dec(x_321);
x_323 = lean_nat_dec_eq(x_322, x_8);
lean_dec(x_322);
x_264 = x_323;
goto block_318;
}
block_318:
{
uint8_t x_265; 
x_265 = l_coeDecidableEq(x_264);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_263);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_266;
}
else
{
lean_object* x_267; uint8_t x_268; lean_object* x_311; uint8_t x_312; 
x_267 = l_Lean_Syntax_getArg(x_263, x_13);
lean_dec(x_263);
x_311 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_267);
x_312 = l_Lean_Syntax_isOfKind(x_267, x_311);
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = 0;
x_268 = x_313;
goto block_310;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l_Lean_Syntax_getArgs(x_267);
x_315 = lean_array_get_size(x_314);
lean_dec(x_314);
x_316 = lean_unsigned_to_nat(3u);
x_317 = lean_nat_dec_eq(x_315, x_316);
lean_dec(x_315);
x_268 = x_317;
goto block_310;
}
block_310:
{
uint8_t x_269; 
x_269 = l_coeDecidableEq(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_270;
}
else
{
lean_object* x_271; uint8_t x_272; uint8_t x_305; 
x_271 = l_Lean_Syntax_getArg(x_267, x_13);
lean_inc(x_271);
x_305 = l_Lean_Syntax_isOfKind(x_271, x_179);
if (x_305 == 0)
{
uint8_t x_306; 
x_306 = 0;
x_272 = x_306;
goto block_304;
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = l_Lean_Syntax_getArgs(x_271);
x_308 = lean_array_get_size(x_307);
lean_dec(x_307);
x_309 = lean_nat_dec_eq(x_308, x_8);
lean_dec(x_308);
x_272 = x_309;
goto block_304;
}
block_304:
{
uint8_t x_273; 
x_273 = l_coeDecidableEq(x_272);
if (x_273 == 0)
{
lean_object* x_274; 
lean_dec(x_271);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_274;
}
else
{
lean_object* x_275; uint8_t x_276; lean_object* x_298; uint8_t x_299; 
x_275 = l_Lean_Syntax_getArg(x_271, x_13);
lean_dec(x_271);
x_298 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_275);
x_299 = l_Lean_Syntax_isOfKind(x_275, x_298);
if (x_299 == 0)
{
uint8_t x_300; 
x_300 = 0;
x_276 = x_300;
goto block_297;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = l_Lean_Syntax_getArgs(x_275);
x_302 = lean_array_get_size(x_301);
lean_dec(x_301);
x_303 = lean_nat_dec_eq(x_302, x_15);
lean_dec(x_302);
x_276 = x_303;
goto block_297;
}
block_297:
{
uint8_t x_277; 
x_277 = l_coeDecidableEq(x_276);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec(x_275);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_278 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; uint8_t x_282; 
x_279 = l_Lean_Syntax_getArg(x_275, x_13);
x_280 = l_Lean_identKind___closed__2;
lean_inc(x_279);
x_281 = l_Lean_Syntax_isOfKind(x_279, x_280);
x_282 = l_coeDecidableEq(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_279);
lean_dec(x_275);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_283;
}
else
{
lean_object* x_284; uint8_t x_285; 
x_284 = l_Lean_Syntax_getArg(x_275, x_8);
lean_dec(x_275);
lean_inc(x_284);
x_285 = l_Lean_Syntax_isOfKind(x_284, x_179);
if (x_285 == 0)
{
uint8_t x_286; 
lean_dec(x_284);
x_286 = l_Lean_Elab_Term_elabParen___closed__4;
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec(x_279);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = l_Lean_Syntax_getArg(x_267, x_15);
lean_dec(x_267);
x_289 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_14, x_279, x_288, x_2, x_3, x_4);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = l_Lean_Syntax_getArgs(x_284);
lean_dec(x_284);
x_291 = lean_array_get_size(x_290);
lean_dec(x_290);
x_292 = lean_nat_dec_eq(x_291, x_13);
lean_dec(x_291);
x_293 = l_coeDecidableEq(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_279);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = l_Lean_Syntax_getArg(x_267, x_15);
lean_dec(x_267);
x_296 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_14, x_279, x_295, x_2, x_3, x_4);
return x_296;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabMatch");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5);
l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6 = _init_l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__6);
l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1 = _init_l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1);
l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2 = _init_l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
