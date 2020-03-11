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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
lean_object* l___private_Init_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
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
x_34 = l_Lean_Elab_Term_elabTerm(x_28, x_5, x_33, x_6, x_11);
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
x_52 = l_Lean_Elab_Term_elabTerm(x_28, x_5, x_51, x_50, x_11);
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
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_6, x_41, x_7, x_12);
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
x_60 = l_Lean_Elab_Term_elabTerm(x_36, x_6, x_59, x_58, x_12);
return x_60;
}
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_297; uint8_t x_298; 
x_297 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_inc(x_1);
x_298 = l_Lean_Syntax_isOfKind(x_1, x_297);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = 0;
x_5 = x_299;
goto block_296;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_300 = l_Lean_Syntax_getArgs(x_1);
x_301 = lean_array_get_size(x_300);
lean_dec(x_300);
x_302 = lean_unsigned_to_nat(6u);
x_303 = lean_nat_dec_eq(x_301, x_302);
lean_dec(x_301);
x_5 = x_303;
goto block_296;
}
block_296:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_290; uint8_t x_291; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_290 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_291 = l_Lean_Syntax_isOfKind(x_8, x_290);
if (x_291 == 0)
{
uint8_t x_292; 
x_292 = 0;
x_9 = x_292;
goto block_289;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = l_Lean_Syntax_getArgs(x_8);
x_294 = lean_array_get_size(x_293);
lean_dec(x_293);
x_295 = lean_nat_dec_eq(x_294, x_7);
lean_dec(x_294);
x_9 = x_295;
goto block_289;
}
block_289:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_155; uint8_t x_156; uint8_t x_157; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_8, x_11);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_155 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_156 = l_Lean_Syntax_isOfKind(x_14, x_155);
if (x_156 == 0)
{
uint8_t x_285; 
x_285 = 0;
x_157 = x_285;
goto block_284;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = l_Lean_Syntax_getArgs(x_14);
x_287 = lean_array_get_size(x_286);
lean_dec(x_286);
x_288 = lean_nat_dec_eq(x_287, x_11);
lean_dec(x_287);
x_157 = x_288;
goto block_284;
}
block_154:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_148; uint8_t x_149; 
x_17 = l_Lean_Syntax_getArg(x_14, x_11);
lean_dec(x_14);
x_148 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_17);
x_149 = l_Lean_Syntax_isOfKind(x_17, x_148);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = 0;
x_18 = x_150;
goto block_147;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = l_Lean_Syntax_getArgs(x_17);
x_152 = lean_array_get_size(x_151);
lean_dec(x_151);
x_153 = lean_nat_dec_eq(x_152, x_13);
lean_dec(x_152);
x_18 = x_153;
goto block_147;
}
block_147:
{
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_82; uint8_t x_83; uint8_t x_84; 
x_20 = l_Lean_Syntax_getArg(x_17, x_7);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_82 = l_Lean_nullKind___closed__2;
lean_inc(x_22);
x_83 = l_Lean_Syntax_isOfKind(x_22, x_82);
if (x_83 == 0)
{
uint8_t x_143; 
x_143 = 0;
x_84 = x_143;
goto block_142;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = l_Lean_Syntax_getArgs(x_22);
x_145 = lean_array_get_size(x_144);
lean_dec(x_144);
x_146 = lean_nat_dec_eq(x_145, x_11);
lean_dec(x_145);
x_84 = x_146;
goto block_142;
}
block_81:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_75; uint8_t x_76; 
x_25 = lean_unsigned_to_nat(5u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_75 = l_Lean_nullKind___closed__2;
lean_inc(x_26);
x_76 = l_Lean_Syntax_isOfKind(x_26, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
x_27 = x_77;
goto block_74;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = l_Lean_Syntax_getArgs(x_26);
x_79 = lean_array_get_size(x_78);
lean_dec(x_78);
x_80 = lean_nat_dec_eq(x_79, x_7);
lean_dec(x_79);
x_27 = x_80;
goto block_74;
}
block_74:
{
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_67; uint8_t x_68; 
x_29 = l_Lean_Syntax_getArg(x_26, x_11);
lean_dec(x_26);
x_67 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_29);
x_68 = l_Lean_Syntax_isOfKind(x_29, x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_30 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = l_Lean_Syntax_getArgs(x_29);
x_71 = lean_array_get_size(x_70);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_dec_eq(x_71, x_72);
lean_dec(x_71);
x_30 = x_73;
goto block_66;
}
block_66:
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_60; uint8_t x_61; 
x_32 = l_Lean_Syntax_getArg(x_29, x_11);
x_60 = l_Lean_nullKind___closed__2;
lean_inc(x_32);
x_61 = l_Lean_Syntax_isOfKind(x_32, x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 0;
x_33 = x_62;
goto block_59;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Syntax_getArgs(x_32);
x_64 = lean_array_get_size(x_63);
lean_dec(x_63);
x_65 = lean_nat_dec_eq(x_64, x_7);
lean_dec(x_64);
x_33 = x_65;
goto block_59;
}
block_59:
{
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_53; uint8_t x_54; 
x_35 = l_Lean_Syntax_getArg(x_32, x_11);
lean_dec(x_32);
x_53 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_35);
x_54 = l_Lean_Syntax_isOfKind(x_35, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_36 = x_55;
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_Syntax_getArgs(x_35);
x_57 = lean_array_get_size(x_56);
lean_dec(x_56);
x_58 = lean_nat_dec_eq(x_57, x_13);
lean_dec(x_57);
x_36 = x_58;
goto block_52;
}
block_52:
{
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Syntax_getArg(x_35, x_11);
x_39 = l_Lean_identKind___closed__2;
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Syntax_getArg(x_35, x_7);
lean_dec(x_35);
x_43 = l_Lean_nullKind___closed__2;
lean_inc(x_42);
x_44 = l_Lean_Syntax_isOfKind(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Syntax_getArgs(x_42);
lean_dec(x_42);
x_47 = lean_array_get_size(x_46);
lean_dec(x_46);
x_48 = lean_nat_dec_eq(x_47, x_11);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Syntax_getArg(x_29, x_13);
lean_dec(x_29);
x_51 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_12, x_38, x_20, x_50, x_2, x_3, x_4);
return x_51;
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
block_142:
{
if (x_84 == 0)
{
if (x_83 == 0)
{
uint8_t x_85; 
lean_dec(x_22);
x_85 = 0;
x_23 = x_85;
goto block_81;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_87 = lean_array_get_size(x_86);
lean_dec(x_86);
x_88 = lean_nat_dec_eq(x_87, x_7);
lean_dec(x_87);
x_23 = x_88;
goto block_81;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_137; 
lean_dec(x_22);
x_89 = lean_unsigned_to_nat(5u);
x_90 = l_Lean_Syntax_getArg(x_1, x_89);
lean_inc(x_90);
x_137 = l_Lean_Syntax_isOfKind(x_90, x_82);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = 0;
x_91 = x_138;
goto block_136;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = l_Lean_Syntax_getArgs(x_90);
x_140 = lean_array_get_size(x_139);
lean_dec(x_139);
x_141 = lean_nat_dec_eq(x_140, x_7);
lean_dec(x_140);
x_91 = x_141;
goto block_136;
}
block_136:
{
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_92;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_129; uint8_t x_130; 
x_93 = l_Lean_Syntax_getArg(x_90, x_11);
lean_dec(x_90);
x_129 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_93);
x_130 = l_Lean_Syntax_isOfKind(x_93, x_129);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = 0;
x_94 = x_131;
goto block_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = l_Lean_Syntax_getArgs(x_93);
x_133 = lean_array_get_size(x_132);
lean_dec(x_132);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_nat_dec_eq(x_133, x_134);
lean_dec(x_133);
x_94 = x_135;
goto block_128;
}
block_128:
{
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_123; 
x_96 = l_Lean_Syntax_getArg(x_93, x_11);
lean_inc(x_96);
x_123 = l_Lean_Syntax_isOfKind(x_96, x_82);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = 0;
x_97 = x_124;
goto block_122;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArgs(x_96);
x_126 = lean_array_get_size(x_125);
lean_dec(x_125);
x_127 = lean_nat_dec_eq(x_126, x_7);
lean_dec(x_126);
x_97 = x_127;
goto block_122;
}
block_122:
{
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_116; uint8_t x_117; 
x_99 = l_Lean_Syntax_getArg(x_96, x_11);
lean_dec(x_96);
x_116 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_99);
x_117 = l_Lean_Syntax_isOfKind(x_99, x_116);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = 0;
x_100 = x_118;
goto block_115;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = l_Lean_Syntax_getArgs(x_99);
x_120 = lean_array_get_size(x_119);
lean_dec(x_119);
x_121 = lean_nat_dec_eq(x_120, x_13);
lean_dec(x_120);
x_100 = x_121;
goto block_115;
}
block_115:
{
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_Syntax_getArg(x_99, x_11);
x_103 = l_Lean_identKind___closed__2;
lean_inc(x_102);
x_104 = l_Lean_Syntax_isOfKind(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_105;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_Syntax_getArg(x_99, x_7);
lean_dec(x_99);
lean_inc(x_106);
x_107 = l_Lean_Syntax_isOfKind(x_106, x_82);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_106);
lean_dec(x_102);
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = l_Lean_Syntax_getArgs(x_106);
lean_dec(x_106);
x_110 = lean_array_get_size(x_109);
lean_dec(x_109);
x_111 = lean_nat_dec_eq(x_110, x_11);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_102);
lean_dec(x_93);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Lean_Syntax_getArg(x_93, x_13);
lean_dec(x_93);
x_114 = l___private_Init_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_12, x_102, x_20, x_113, x_2, x_3, x_4);
return x_114;
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
block_284:
{
if (x_157 == 0)
{
if (x_156 == 0)
{
uint8_t x_158; 
x_158 = 0;
x_15 = x_158;
goto block_154;
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = l_Lean_Syntax_getArgs(x_14);
x_160 = lean_array_get_size(x_159);
lean_dec(x_159);
x_161 = lean_nat_dec_eq(x_160, x_7);
lean_dec(x_160);
x_15 = x_161;
goto block_154;
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_220; uint8_t x_221; 
lean_dec(x_14);
x_162 = lean_unsigned_to_nat(4u);
x_163 = l_Lean_Syntax_getArg(x_1, x_162);
lean_inc(x_163);
x_220 = l_Lean_Syntax_isOfKind(x_163, x_155);
if (x_220 == 0)
{
uint8_t x_280; 
x_280 = 0;
x_221 = x_280;
goto block_279;
}
else
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_281 = l_Lean_Syntax_getArgs(x_163);
x_282 = lean_array_get_size(x_281);
lean_dec(x_281);
x_283 = lean_nat_dec_eq(x_282, x_11);
lean_dec(x_282);
x_221 = x_283;
goto block_279;
}
block_219:
{
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_214; 
x_166 = lean_unsigned_to_nat(5u);
x_167 = l_Lean_Syntax_getArg(x_1, x_166);
lean_inc(x_167);
x_214 = l_Lean_Syntax_isOfKind(x_167, x_155);
if (x_214 == 0)
{
uint8_t x_215; 
x_215 = 0;
x_168 = x_215;
goto block_213;
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = l_Lean_Syntax_getArgs(x_167);
x_217 = lean_array_get_size(x_216);
lean_dec(x_216);
x_218 = lean_nat_dec_eq(x_217, x_7);
lean_dec(x_217);
x_168 = x_218;
goto block_213;
}
block_213:
{
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_167);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_169;
}
else
{
lean_object* x_170; uint8_t x_171; lean_object* x_206; uint8_t x_207; 
x_170 = l_Lean_Syntax_getArg(x_167, x_11);
lean_dec(x_167);
x_206 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_170);
x_207 = l_Lean_Syntax_isOfKind(x_170, x_206);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = 0;
x_171 = x_208;
goto block_205;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = l_Lean_Syntax_getArgs(x_170);
x_210 = lean_array_get_size(x_209);
lean_dec(x_209);
x_211 = lean_unsigned_to_nat(3u);
x_212 = lean_nat_dec_eq(x_210, x_211);
lean_dec(x_210);
x_171 = x_212;
goto block_205;
}
block_205:
{
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_172;
}
else
{
lean_object* x_173; uint8_t x_174; uint8_t x_200; 
x_173 = l_Lean_Syntax_getArg(x_170, x_11);
lean_inc(x_173);
x_200 = l_Lean_Syntax_isOfKind(x_173, x_155);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = 0;
x_174 = x_201;
goto block_199;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = l_Lean_Syntax_getArgs(x_173);
x_203 = lean_array_get_size(x_202);
lean_dec(x_202);
x_204 = lean_nat_dec_eq(x_203, x_7);
lean_dec(x_203);
x_174 = x_204;
goto block_199;
}
block_199:
{
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_175;
}
else
{
lean_object* x_176; uint8_t x_177; lean_object* x_193; uint8_t x_194; 
x_176 = l_Lean_Syntax_getArg(x_173, x_11);
lean_dec(x_173);
x_193 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_176);
x_194 = l_Lean_Syntax_isOfKind(x_176, x_193);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = 0;
x_177 = x_195;
goto block_192;
}
else
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = l_Lean_Syntax_getArgs(x_176);
x_197 = lean_array_get_size(x_196);
lean_dec(x_196);
x_198 = lean_nat_dec_eq(x_197, x_13);
lean_dec(x_197);
x_177 = x_198;
goto block_192;
}
block_192:
{
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Lean_Syntax_getArg(x_176, x_11);
x_180 = l_Lean_identKind___closed__2;
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = l_Lean_Syntax_getArg(x_176, x_7);
lean_dec(x_176);
lean_inc(x_183);
x_184 = l_Lean_Syntax_isOfKind(x_183, x_155);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_183);
lean_dec(x_179);
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = l_Lean_Syntax_getArgs(x_183);
lean_dec(x_183);
x_187 = lean_array_get_size(x_186);
lean_dec(x_186);
x_188 = lean_nat_dec_eq(x_187, x_11);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_179);
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Lean_Syntax_getArg(x_170, x_13);
lean_dec(x_170);
x_191 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_12, x_179, x_190, x_2, x_3, x_4);
return x_191;
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
block_279:
{
if (x_221 == 0)
{
if (x_220 == 0)
{
uint8_t x_222; 
lean_dec(x_163);
x_222 = 0;
x_164 = x_222;
goto block_219;
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = l_Lean_Syntax_getArgs(x_163);
lean_dec(x_163);
x_224 = lean_array_get_size(x_223);
lean_dec(x_223);
x_225 = lean_nat_dec_eq(x_224, x_7);
lean_dec(x_224);
x_164 = x_225;
goto block_219;
}
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_274; 
lean_dec(x_163);
x_226 = lean_unsigned_to_nat(5u);
x_227 = l_Lean_Syntax_getArg(x_1, x_226);
lean_inc(x_227);
x_274 = l_Lean_Syntax_isOfKind(x_227, x_155);
if (x_274 == 0)
{
uint8_t x_275; 
x_275 = 0;
x_228 = x_275;
goto block_273;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = l_Lean_Syntax_getArgs(x_227);
x_277 = lean_array_get_size(x_276);
lean_dec(x_276);
x_278 = lean_nat_dec_eq(x_277, x_7);
lean_dec(x_277);
x_228 = x_278;
goto block_273;
}
block_273:
{
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_227);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_229;
}
else
{
lean_object* x_230; uint8_t x_231; lean_object* x_266; uint8_t x_267; 
x_230 = l_Lean_Syntax_getArg(x_227, x_11);
lean_dec(x_227);
x_266 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_230);
x_267 = l_Lean_Syntax_isOfKind(x_230, x_266);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = 0;
x_231 = x_268;
goto block_265;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = l_Lean_Syntax_getArgs(x_230);
x_270 = lean_array_get_size(x_269);
lean_dec(x_269);
x_271 = lean_unsigned_to_nat(3u);
x_272 = lean_nat_dec_eq(x_270, x_271);
lean_dec(x_270);
x_231 = x_272;
goto block_265;
}
block_265:
{
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_232 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_232;
}
else
{
lean_object* x_233; uint8_t x_234; uint8_t x_260; 
x_233 = l_Lean_Syntax_getArg(x_230, x_11);
lean_inc(x_233);
x_260 = l_Lean_Syntax_isOfKind(x_233, x_155);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = 0;
x_234 = x_261;
goto block_259;
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = l_Lean_Syntax_getArgs(x_233);
x_263 = lean_array_get_size(x_262);
lean_dec(x_262);
x_264 = lean_nat_dec_eq(x_263, x_7);
lean_dec(x_263);
x_234 = x_264;
goto block_259;
}
block_259:
{
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_233);
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_235;
}
else
{
lean_object* x_236; uint8_t x_237; lean_object* x_253; uint8_t x_254; 
x_236 = l_Lean_Syntax_getArg(x_233, x_11);
lean_dec(x_233);
x_253 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_236);
x_254 = l_Lean_Syntax_isOfKind(x_236, x_253);
if (x_254 == 0)
{
uint8_t x_255; 
x_255 = 0;
x_237 = x_255;
goto block_252;
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = l_Lean_Syntax_getArgs(x_236);
x_257 = lean_array_get_size(x_256);
lean_dec(x_256);
x_258 = lean_nat_dec_eq(x_257, x_13);
lean_dec(x_257);
x_237 = x_258;
goto block_252;
}
block_252:
{
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_236);
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = l_Lean_Syntax_getArg(x_236, x_11);
x_240 = l_Lean_identKind___closed__2;
lean_inc(x_239);
x_241 = l_Lean_Syntax_isOfKind(x_239, x_240);
if (x_241 == 0)
{
lean_object* x_242; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_242;
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = l_Lean_Syntax_getArg(x_236, x_7);
lean_dec(x_236);
lean_inc(x_243);
x_244 = l_Lean_Syntax_isOfKind(x_243, x_155);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_243);
lean_dec(x_239);
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = l_Lean_Syntax_getArgs(x_243);
lean_dec(x_243);
x_247 = lean_array_get_size(x_246);
lean_dec(x_246);
x_248 = lean_nat_dec_eq(x_247, x_11);
lean_dec(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_239);
lean_dec(x_230);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Lean_Syntax_getArg(x_230, x_13);
lean_dec(x_230);
x_251 = l___private_Init_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_12, x_239, x_250, x_2, x_3, x_4);
return x_251;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
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
res = l___regBuiltinTermElab_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
