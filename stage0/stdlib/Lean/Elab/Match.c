// Lean compiler output
// Module: Lean.Elab.Match
// Imports: Init Lean.Elab.Term
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
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___private_Lean_Elab_Match_3__elabMatchCore___spec__2(lean_object*);
extern lean_object* l_IO_FS_Handle_putStrLn___rarg___closed__1;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___closed__2;
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_let___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_15 = lean_array_push(x_13, x_14);
x_16 = lean_array_push(x_15, x_14);
x_17 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
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
x_34 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_33, x_33, x_28, x_6, x_11);
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
x_52 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_51, x_51, x_28, x_50, x_11);
return x_52;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_16 = lean_array_push(x_14, x_15);
x_17 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
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
x_25 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_array_push(x_26, x_2);
x_28 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
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
x_42 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_41, x_41, x_36, x_7, x_12);
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
x_60 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_59, x_59, x_36, x_58, x_12);
return x_60;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_9, x_10);
lean_dec(x_9);
x_12 = lean_nat_add(x_1, x_10);
x_13 = x_11;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux___main(x_6, x_7, x_8, x_4);
x_10 = l_Lean_Options_empty;
x_11 = l_Lean_Format_pretty(x_9, x_10);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(x_1, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; 
x_16 = l_String_splitAux___main___closed__1;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = 0;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_formatStxAux___main(x_19, x_20, x_21, x_17);
x_23 = l_Lean_Options_empty;
x_24 = l_Lean_Format_pretty(x_22, x_23);
x_25 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(x_20, x_18);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
}
}
lean_object* l_List_toString___at___private_Lean_Elab_Match_3__elabMatchCore___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabMatchCore___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabMatchCore___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Handle_putStrLn___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_3__elabMatchCore___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_8, x_7, x_9, x_10);
lean_dec(x_7);
x_12 = x_11;
x_13 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__1(x_9, x_12);
x_14 = x_13;
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l___private_Lean_Elab_Match_3__elabMatchCore___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_Match_3__elabMatchCore___closed__5;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
x_21 = l_List_toString___at___private_Lean_Elab_Match_3__elabMatchCore___spec__2(x_20);
x_22 = l_Array_HasRepr___rarg___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Term_throwError___rarg(x_1, x_26, x_3, x_28);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_3__elabMatchCore___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_3__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__elabMatchCore(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg), 1, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_9; lean_object* x_878; uint8_t x_879; 
x_878 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_inc(x_1);
x_879 = l_Lean_Syntax_isOfKind(x_1, x_878);
if (x_879 == 0)
{
uint8_t x_880; 
x_880 = 0;
x_9 = x_880;
goto block_877;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; 
x_881 = l_Lean_Syntax_getArgs(x_1);
x_882 = lean_array_get_size(x_881);
lean_dec(x_881);
x_883 = lean_unsigned_to_nat(6u);
x_884 = lean_nat_dec_eq(x_882, x_883);
lean_dec(x_882);
x_9 = x_884;
goto block_877;
}
block_8:
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l___private_Lean_Elab_Match_3__elabMatchCore(x_1, x_2, x_3, x_6);
lean_dec(x_2);
return x_7;
}
block_877:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_getEnv___rarg(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 5);
x_16 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_13, 5, x_18);
x_5 = x_17;
x_6 = x_13;
goto block_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 2);
x_22 = lean_ctor_get(x_13, 3);
x_23 = lean_ctor_get(x_13, 4);
x_24 = lean_ctor_get(x_13, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_25 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_27);
x_5 = x_26;
x_6 = x_28;
goto block_8;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_870; uint8_t x_871; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_870 = l_Lean_nullKind___closed__2;
lean_inc(x_30);
x_871 = l_Lean_Syntax_isOfKind(x_30, x_870);
if (x_871 == 0)
{
uint8_t x_872; 
x_872 = 0;
x_31 = x_872;
goto block_869;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; uint8_t x_876; 
x_873 = l_Lean_Syntax_getArgs(x_30);
x_874 = lean_array_get_size(x_873);
lean_dec(x_873);
x_875 = lean_unsigned_to_nat(2u);
x_876 = lean_nat_dec_eq(x_874, x_875);
lean_dec(x_874);
x_31 = x_876;
goto block_869;
}
block_869:
{
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_30);
x_32 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Term_getEnv___rarg(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 5);
x_38 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_ctor_set(x_35, 5, x_40);
x_5 = x_39;
x_6 = x_35;
goto block_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
x_43 = lean_ctor_get(x_35, 2);
x_44 = lean_ctor_get(x_35, 3);
x_45 = lean_ctor_get(x_35, 4);
x_46 = lean_ctor_get(x_35, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_47 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_49);
x_5 = x_48;
x_6 = x_50;
goto block_8;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_863; uint8_t x_864; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_30, x_51);
x_863 = l_Lean_nullKind___closed__2;
lean_inc(x_52);
x_864 = l_Lean_Syntax_isOfKind(x_52, x_863);
if (x_864 == 0)
{
uint8_t x_865; 
lean_dec(x_52);
x_865 = 0;
x_53 = x_865;
goto block_862;
}
else
{
lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_866 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_867 = lean_array_get_size(x_866);
lean_dec(x_866);
x_868 = lean_nat_dec_eq(x_867, x_51);
lean_dec(x_867);
x_53 = x_868;
goto block_862;
}
block_862:
{
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_30);
x_54 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Elab_Term_getEnv___rarg(x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_57, 5);
x_60 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_ctor_set(x_57, 5, x_62);
x_5 = x_61;
x_6 = x_57;
goto block_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
x_65 = lean_ctor_get(x_57, 2);
x_66 = lean_ctor_get(x_57, 3);
x_67 = lean_ctor_get(x_57, 4);
x_68 = lean_ctor_get(x_57, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_69 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_65);
lean_ctor_set(x_72, 3, x_66);
lean_ctor_set(x_72, 4, x_67);
lean_ctor_set(x_72, 5, x_71);
x_5 = x_70;
x_6 = x_72;
goto block_8;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_490; uint8_t x_491; uint8_t x_492; 
x_73 = l_Lean_Syntax_getArg(x_30, x_29);
lean_dec(x_30);
x_74 = lean_unsigned_to_nat(2u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
x_490 = l_Lean_nullKind___closed__2;
lean_inc(x_75);
x_491 = l_Lean_Syntax_isOfKind(x_75, x_490);
if (x_491 == 0)
{
uint8_t x_858; 
x_858 = 0;
x_492 = x_858;
goto block_857;
}
else
{
lean_object* x_859; lean_object* x_860; uint8_t x_861; 
x_859 = l_Lean_Syntax_getArgs(x_75);
x_860 = lean_array_get_size(x_859);
lean_dec(x_859);
x_861 = lean_nat_dec_eq(x_860, x_51);
lean_dec(x_860);
x_492 = x_861;
goto block_857;
}
block_489:
{
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_75);
lean_dec(x_73);
x_77 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Term_getEnv___rarg(x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_80, 5);
x_83 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_ctor_set(x_80, 5, x_85);
x_5 = x_84;
x_6 = x_80;
goto block_8;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
x_88 = lean_ctor_get(x_80, 2);
x_89 = lean_ctor_get(x_80, 3);
x_90 = lean_ctor_get(x_80, 4);
x_91 = lean_ctor_get(x_80, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_92 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_86);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_88);
lean_ctor_set(x_95, 3, x_89);
lean_ctor_set(x_95, 4, x_90);
lean_ctor_set(x_95, 5, x_94);
x_5 = x_93;
x_6 = x_95;
goto block_8;
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_483; uint8_t x_484; 
x_96 = l_Lean_Syntax_getArg(x_75, x_51);
lean_dec(x_75);
x_483 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_96);
x_484 = l_Lean_Syntax_isOfKind(x_96, x_483);
if (x_484 == 0)
{
uint8_t x_485; 
x_485 = 0;
x_97 = x_485;
goto block_482;
}
else
{
lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_486 = l_Lean_Syntax_getArgs(x_96);
x_487 = lean_array_get_size(x_486);
lean_dec(x_486);
x_488 = lean_nat_dec_eq(x_487, x_74);
lean_dec(x_487);
x_97 = x_488;
goto block_482;
}
block_482:
{
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_96);
lean_dec(x_73);
x_98 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Elab_Term_getEnv___rarg(x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_101, 5);
x_104 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_ctor_set(x_101, 5, x_106);
x_5 = x_105;
x_6 = x_101;
goto block_8;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_101, 0);
x_108 = lean_ctor_get(x_101, 1);
x_109 = lean_ctor_get(x_101, 2);
x_110 = lean_ctor_get(x_101, 3);
x_111 = lean_ctor_get(x_101, 4);
x_112 = lean_ctor_get(x_101, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_101);
x_113 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set(x_116, 2, x_109);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set(x_116, 5, x_115);
x_5 = x_114;
x_6 = x_116;
goto block_8;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_307; uint8_t x_308; uint8_t x_309; 
x_117 = l_Lean_Syntax_getArg(x_96, x_29);
lean_dec(x_96);
x_118 = lean_unsigned_to_nat(4u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
x_307 = l_Lean_nullKind___closed__2;
lean_inc(x_119);
x_308 = l_Lean_Syntax_isOfKind(x_119, x_307);
if (x_308 == 0)
{
uint8_t x_478; 
x_478 = 0;
x_309 = x_478;
goto block_477;
}
else
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; 
x_479 = l_Lean_Syntax_getArgs(x_119);
x_480 = lean_array_get_size(x_479);
lean_dec(x_479);
x_481 = lean_nat_dec_eq(x_480, x_51);
lean_dec(x_480);
x_309 = x_481;
goto block_477;
}
block_306:
{
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_117);
lean_dec(x_73);
x_121 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_Elab_Term_getEnv___rarg(x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_124, 5);
x_127 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_ctor_set(x_124, 5, x_129);
x_5 = x_128;
x_6 = x_124;
goto block_8;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = lean_ctor_get(x_124, 0);
x_131 = lean_ctor_get(x_124, 1);
x_132 = lean_ctor_get(x_124, 2);
x_133 = lean_ctor_get(x_124, 3);
x_134 = lean_ctor_get(x_124, 4);
x_135 = lean_ctor_get(x_124, 5);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_124);
x_136 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_132);
lean_ctor_set(x_139, 3, x_133);
lean_ctor_set(x_139, 4, x_134);
lean_ctor_set(x_139, 5, x_138);
x_5 = x_137;
x_6 = x_139;
goto block_8;
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_300; uint8_t x_301; 
x_140 = lean_unsigned_to_nat(5u);
x_141 = l_Lean_Syntax_getArg(x_1, x_140);
x_300 = l_Lean_nullKind___closed__2;
lean_inc(x_141);
x_301 = l_Lean_Syntax_isOfKind(x_141, x_300);
if (x_301 == 0)
{
uint8_t x_302; 
x_302 = 0;
x_142 = x_302;
goto block_299;
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = l_Lean_Syntax_getArgs(x_141);
x_304 = lean_array_get_size(x_303);
lean_dec(x_303);
x_305 = lean_nat_dec_eq(x_304, x_29);
lean_dec(x_304);
x_142 = x_305;
goto block_299;
}
block_299:
{
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_141);
lean_dec(x_117);
lean_dec(x_73);
x_143 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Lean_Elab_Term_getEnv___rarg(x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_146, 5);
x_149 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_ctor_set(x_146, 5, x_151);
x_5 = x_150;
x_6 = x_146;
goto block_8;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_146, 0);
x_153 = lean_ctor_get(x_146, 1);
x_154 = lean_ctor_get(x_146, 2);
x_155 = lean_ctor_get(x_146, 3);
x_156 = lean_ctor_get(x_146, 4);
x_157 = lean_ctor_get(x_146, 5);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_146);
x_158 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_155);
lean_ctor_set(x_161, 4, x_156);
lean_ctor_set(x_161, 5, x_160);
x_5 = x_159;
x_6 = x_161;
goto block_8;
}
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_292; uint8_t x_293; 
x_162 = l_Lean_Syntax_getArg(x_141, x_51);
lean_dec(x_141);
x_292 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_162);
x_293 = l_Lean_Syntax_isOfKind(x_162, x_292);
if (x_293 == 0)
{
uint8_t x_294; 
x_294 = 0;
x_163 = x_294;
goto block_291;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_295 = l_Lean_Syntax_getArgs(x_162);
x_296 = lean_array_get_size(x_295);
lean_dec(x_295);
x_297 = lean_unsigned_to_nat(3u);
x_298 = lean_nat_dec_eq(x_296, x_297);
lean_dec(x_296);
x_163 = x_298;
goto block_291;
}
block_291:
{
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_162);
lean_dec(x_117);
lean_dec(x_73);
x_164 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Elab_Term_getEnv___rarg(x_165);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_167, 5);
x_170 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_ctor_set(x_167, 5, x_172);
x_5 = x_171;
x_6 = x_167;
goto block_8;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_ctor_get(x_167, 0);
x_174 = lean_ctor_get(x_167, 1);
x_175 = lean_ctor_get(x_167, 2);
x_176 = lean_ctor_get(x_167, 3);
x_177 = lean_ctor_get(x_167, 4);
x_178 = lean_ctor_get(x_167, 5);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_167);
x_179 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_182, 0, x_173);
lean_ctor_set(x_182, 1, x_174);
lean_ctor_set(x_182, 2, x_175);
lean_ctor_set(x_182, 3, x_176);
lean_ctor_set(x_182, 4, x_177);
lean_ctor_set(x_182, 5, x_181);
x_5 = x_180;
x_6 = x_182;
goto block_8;
}
}
else
{
lean_object* x_183; uint8_t x_184; lean_object* x_285; uint8_t x_286; 
x_183 = l_Lean_Syntax_getArg(x_162, x_51);
x_285 = l_Lean_nullKind___closed__2;
lean_inc(x_183);
x_286 = l_Lean_Syntax_isOfKind(x_183, x_285);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = 0;
x_184 = x_287;
goto block_284;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = l_Lean_Syntax_getArgs(x_183);
x_289 = lean_array_get_size(x_288);
lean_dec(x_288);
x_290 = lean_nat_dec_eq(x_289, x_29);
lean_dec(x_289);
x_184 = x_290;
goto block_284;
}
block_284:
{
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_183);
lean_dec(x_162);
lean_dec(x_117);
lean_dec(x_73);
x_185 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Elab_Term_getEnv___rarg(x_186);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_188, 5);
x_191 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_ctor_set(x_188, 5, x_193);
x_5 = x_192;
x_6 = x_188;
goto block_8;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_194 = lean_ctor_get(x_188, 0);
x_195 = lean_ctor_get(x_188, 1);
x_196 = lean_ctor_get(x_188, 2);
x_197 = lean_ctor_get(x_188, 3);
x_198 = lean_ctor_get(x_188, 4);
x_199 = lean_ctor_get(x_188, 5);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_188);
x_200 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_195);
lean_ctor_set(x_203, 2, x_196);
lean_ctor_set(x_203, 3, x_197);
lean_ctor_set(x_203, 4, x_198);
lean_ctor_set(x_203, 5, x_202);
x_5 = x_201;
x_6 = x_203;
goto block_8;
}
}
else
{
lean_object* x_204; uint8_t x_205; lean_object* x_278; uint8_t x_279; 
x_204 = l_Lean_Syntax_getArg(x_183, x_51);
lean_dec(x_183);
x_278 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_204);
x_279 = l_Lean_Syntax_isOfKind(x_204, x_278);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = 0;
x_205 = x_280;
goto block_277;
}
else
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_281 = l_Lean_Syntax_getArgs(x_204);
x_282 = lean_array_get_size(x_281);
lean_dec(x_281);
x_283 = lean_nat_dec_eq(x_282, x_74);
lean_dec(x_282);
x_205 = x_283;
goto block_277;
}
block_277:
{
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_204);
lean_dec(x_162);
lean_dec(x_117);
lean_dec(x_73);
x_206 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = l_Lean_Elab_Term_getEnv___rarg(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_209, 5);
x_212 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_ctor_set(x_209, 5, x_214);
x_5 = x_213;
x_6 = x_209;
goto block_8;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_215 = lean_ctor_get(x_209, 0);
x_216 = lean_ctor_get(x_209, 1);
x_217 = lean_ctor_get(x_209, 2);
x_218 = lean_ctor_get(x_209, 3);
x_219 = lean_ctor_get(x_209, 4);
x_220 = lean_ctor_get(x_209, 5);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_209);
x_221 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_224, 0, x_215);
lean_ctor_set(x_224, 1, x_216);
lean_ctor_set(x_224, 2, x_217);
lean_ctor_set(x_224, 3, x_218);
lean_ctor_set(x_224, 4, x_219);
lean_ctor_set(x_224, 5, x_223);
x_5 = x_222;
x_6 = x_224;
goto block_8;
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = l_Lean_Syntax_getArg(x_204, x_51);
x_226 = l_Lean_identKind___closed__2;
lean_inc(x_225);
x_227 = l_Lean_Syntax_isOfKind(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_225);
lean_dec(x_204);
lean_dec(x_162);
lean_dec(x_117);
lean_dec(x_73);
x_228 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = l_Lean_Elab_Term_getEnv___rarg(x_229);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_231, 5);
x_234 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_ctor_set(x_231, 5, x_236);
x_5 = x_235;
x_6 = x_231;
goto block_8;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_237 = lean_ctor_get(x_231, 0);
x_238 = lean_ctor_get(x_231, 1);
x_239 = lean_ctor_get(x_231, 2);
x_240 = lean_ctor_get(x_231, 3);
x_241 = lean_ctor_get(x_231, 4);
x_242 = lean_ctor_get(x_231, 5);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_231);
x_243 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_246, 0, x_237);
lean_ctor_set(x_246, 1, x_238);
lean_ctor_set(x_246, 2, x_239);
lean_ctor_set(x_246, 3, x_240);
lean_ctor_set(x_246, 4, x_241);
lean_ctor_set(x_246, 5, x_245);
x_5 = x_244;
x_6 = x_246;
goto block_8;
}
}
else
{
lean_object* x_247; uint8_t x_248; lean_object* x_271; uint8_t x_272; 
x_247 = l_Lean_Syntax_getArg(x_204, x_29);
lean_dec(x_204);
x_271 = l_Lean_nullKind___closed__2;
lean_inc(x_247);
x_272 = l_Lean_Syntax_isOfKind(x_247, x_271);
if (x_272 == 0)
{
uint8_t x_273; 
lean_dec(x_247);
x_273 = 0;
x_248 = x_273;
goto block_270;
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_274 = l_Lean_Syntax_getArgs(x_247);
lean_dec(x_247);
x_275 = lean_array_get_size(x_274);
lean_dec(x_274);
x_276 = lean_nat_dec_eq(x_275, x_51);
lean_dec(x_275);
x_248 = x_276;
goto block_270;
}
block_270:
{
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_225);
lean_dec(x_162);
lean_dec(x_117);
lean_dec(x_73);
x_249 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_251 = l_Lean_Elab_Term_getEnv___rarg(x_250);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_252, 5);
x_255 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
lean_ctor_set(x_252, 5, x_257);
x_5 = x_256;
x_6 = x_252;
goto block_8;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_258 = lean_ctor_get(x_252, 0);
x_259 = lean_ctor_get(x_252, 1);
x_260 = lean_ctor_get(x_252, 2);
x_261 = lean_ctor_get(x_252, 3);
x_262 = lean_ctor_get(x_252, 4);
x_263 = lean_ctor_get(x_252, 5);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_252);
x_264 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_267, 0, x_258);
lean_ctor_set(x_267, 1, x_259);
lean_ctor_set(x_267, 2, x_260);
lean_ctor_set(x_267, 3, x_261);
lean_ctor_set(x_267, 4, x_262);
lean_ctor_set(x_267, 5, x_266);
x_5 = x_265;
x_6 = x_267;
goto block_8;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = l_Lean_Syntax_getArg(x_162, x_74);
lean_dec(x_162);
x_269 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_73, x_225, x_117, x_268, x_2, x_3, x_4);
return x_269;
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
block_477:
{
if (x_309 == 0)
{
if (x_308 == 0)
{
uint8_t x_310; 
lean_dec(x_119);
x_310 = 0;
x_120 = x_310;
goto block_306;
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = l_Lean_Syntax_getArgs(x_119);
lean_dec(x_119);
x_312 = lean_array_get_size(x_311);
lean_dec(x_311);
x_313 = lean_nat_dec_eq(x_312, x_29);
lean_dec(x_312);
x_120 = x_313;
goto block_306;
}
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; uint8_t x_472; 
lean_dec(x_119);
x_314 = lean_unsigned_to_nat(5u);
x_315 = l_Lean_Syntax_getArg(x_1, x_314);
lean_inc(x_315);
x_472 = l_Lean_Syntax_isOfKind(x_315, x_307);
if (x_472 == 0)
{
uint8_t x_473; 
x_473 = 0;
x_316 = x_473;
goto block_471;
}
else
{
lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_474 = l_Lean_Syntax_getArgs(x_315);
x_475 = lean_array_get_size(x_474);
lean_dec(x_474);
x_476 = lean_nat_dec_eq(x_475, x_29);
lean_dec(x_475);
x_316 = x_476;
goto block_471;
}
block_471:
{
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
lean_dec(x_315);
lean_dec(x_117);
lean_dec(x_73);
x_317 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = l_Lean_Elab_Term_getEnv___rarg(x_318);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_320, 5);
x_323 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_322);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
lean_ctor_set(x_320, 5, x_325);
x_5 = x_324;
x_6 = x_320;
goto block_8;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_320, 0);
x_327 = lean_ctor_get(x_320, 1);
x_328 = lean_ctor_get(x_320, 2);
x_329 = lean_ctor_get(x_320, 3);
x_330 = lean_ctor_get(x_320, 4);
x_331 = lean_ctor_get(x_320, 5);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_320);
x_332 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_331);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_327);
lean_ctor_set(x_335, 2, x_328);
lean_ctor_set(x_335, 3, x_329);
lean_ctor_set(x_335, 4, x_330);
lean_ctor_set(x_335, 5, x_334);
x_5 = x_333;
x_6 = x_335;
goto block_8;
}
}
else
{
lean_object* x_336; uint8_t x_337; lean_object* x_464; uint8_t x_465; 
x_336 = l_Lean_Syntax_getArg(x_315, x_51);
lean_dec(x_315);
x_464 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_336);
x_465 = l_Lean_Syntax_isOfKind(x_336, x_464);
if (x_465 == 0)
{
uint8_t x_466; 
x_466 = 0;
x_337 = x_466;
goto block_463;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_467 = l_Lean_Syntax_getArgs(x_336);
x_468 = lean_array_get_size(x_467);
lean_dec(x_467);
x_469 = lean_unsigned_to_nat(3u);
x_470 = lean_nat_dec_eq(x_468, x_469);
lean_dec(x_468);
x_337 = x_470;
goto block_463;
}
block_463:
{
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_336);
lean_dec(x_117);
lean_dec(x_73);
x_338 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = l_Lean_Elab_Term_getEnv___rarg(x_339);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_341, 5);
x_344 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_343);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
lean_ctor_set(x_341, 5, x_346);
x_5 = x_345;
x_6 = x_341;
goto block_8;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_347 = lean_ctor_get(x_341, 0);
x_348 = lean_ctor_get(x_341, 1);
x_349 = lean_ctor_get(x_341, 2);
x_350 = lean_ctor_get(x_341, 3);
x_351 = lean_ctor_get(x_341, 4);
x_352 = lean_ctor_get(x_341, 5);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_341);
x_353 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_356, 0, x_347);
lean_ctor_set(x_356, 1, x_348);
lean_ctor_set(x_356, 2, x_349);
lean_ctor_set(x_356, 3, x_350);
lean_ctor_set(x_356, 4, x_351);
lean_ctor_set(x_356, 5, x_355);
x_5 = x_354;
x_6 = x_356;
goto block_8;
}
}
else
{
lean_object* x_357; uint8_t x_358; uint8_t x_458; 
x_357 = l_Lean_Syntax_getArg(x_336, x_51);
lean_inc(x_357);
x_458 = l_Lean_Syntax_isOfKind(x_357, x_307);
if (x_458 == 0)
{
uint8_t x_459; 
x_459 = 0;
x_358 = x_459;
goto block_457;
}
else
{
lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_460 = l_Lean_Syntax_getArgs(x_357);
x_461 = lean_array_get_size(x_460);
lean_dec(x_460);
x_462 = lean_nat_dec_eq(x_461, x_29);
lean_dec(x_461);
x_358 = x_462;
goto block_457;
}
block_457:
{
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
lean_dec(x_357);
lean_dec(x_336);
lean_dec(x_117);
lean_dec(x_73);
x_359 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_361 = l_Lean_Elab_Term_getEnv___rarg(x_360);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_362, 5);
x_365 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_364);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
lean_ctor_set(x_362, 5, x_367);
x_5 = x_366;
x_6 = x_362;
goto block_8;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_368 = lean_ctor_get(x_362, 0);
x_369 = lean_ctor_get(x_362, 1);
x_370 = lean_ctor_get(x_362, 2);
x_371 = lean_ctor_get(x_362, 3);
x_372 = lean_ctor_get(x_362, 4);
x_373 = lean_ctor_get(x_362, 5);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_362);
x_374 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_373);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_377, 0, x_368);
lean_ctor_set(x_377, 1, x_369);
lean_ctor_set(x_377, 2, x_370);
lean_ctor_set(x_377, 3, x_371);
lean_ctor_set(x_377, 4, x_372);
lean_ctor_set(x_377, 5, x_376);
x_5 = x_375;
x_6 = x_377;
goto block_8;
}
}
else
{
lean_object* x_378; uint8_t x_379; lean_object* x_451; uint8_t x_452; 
x_378 = l_Lean_Syntax_getArg(x_357, x_51);
lean_dec(x_357);
x_451 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_378);
x_452 = l_Lean_Syntax_isOfKind(x_378, x_451);
if (x_452 == 0)
{
uint8_t x_453; 
x_453 = 0;
x_379 = x_453;
goto block_450;
}
else
{
lean_object* x_454; lean_object* x_455; uint8_t x_456; 
x_454 = l_Lean_Syntax_getArgs(x_378);
x_455 = lean_array_get_size(x_454);
lean_dec(x_454);
x_456 = lean_nat_dec_eq(x_455, x_74);
lean_dec(x_455);
x_379 = x_456;
goto block_450;
}
block_450:
{
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_dec(x_378);
lean_dec(x_336);
lean_dec(x_117);
lean_dec(x_73);
x_380 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = l_Lean_Elab_Term_getEnv___rarg(x_381);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = !lean_is_exclusive(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_383, 5);
x_386 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_ctor_set(x_383, 5, x_388);
x_5 = x_387;
x_6 = x_383;
goto block_8;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_389 = lean_ctor_get(x_383, 0);
x_390 = lean_ctor_get(x_383, 1);
x_391 = lean_ctor_get(x_383, 2);
x_392 = lean_ctor_get(x_383, 3);
x_393 = lean_ctor_get(x_383, 4);
x_394 = lean_ctor_get(x_383, 5);
lean_inc(x_394);
lean_inc(x_393);
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_383);
x_395 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_398, 0, x_389);
lean_ctor_set(x_398, 1, x_390);
lean_ctor_set(x_398, 2, x_391);
lean_ctor_set(x_398, 3, x_392);
lean_ctor_set(x_398, 4, x_393);
lean_ctor_set(x_398, 5, x_397);
x_5 = x_396;
x_6 = x_398;
goto block_8;
}
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_399 = l_Lean_Syntax_getArg(x_378, x_51);
x_400 = l_Lean_identKind___closed__2;
lean_inc(x_399);
x_401 = l_Lean_Syntax_isOfKind(x_399, x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
lean_dec(x_399);
lean_dec(x_378);
lean_dec(x_336);
lean_dec(x_117);
lean_dec(x_73);
x_402 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
lean_dec(x_402);
x_404 = l_Lean_Elab_Term_getEnv___rarg(x_403);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_405, 5);
x_408 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_ctor_set(x_405, 5, x_410);
x_5 = x_409;
x_6 = x_405;
goto block_8;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_411 = lean_ctor_get(x_405, 0);
x_412 = lean_ctor_get(x_405, 1);
x_413 = lean_ctor_get(x_405, 2);
x_414 = lean_ctor_get(x_405, 3);
x_415 = lean_ctor_get(x_405, 4);
x_416 = lean_ctor_get(x_405, 5);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_405);
x_417 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_416);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_420, 0, x_411);
lean_ctor_set(x_420, 1, x_412);
lean_ctor_set(x_420, 2, x_413);
lean_ctor_set(x_420, 3, x_414);
lean_ctor_set(x_420, 4, x_415);
lean_ctor_set(x_420, 5, x_419);
x_5 = x_418;
x_6 = x_420;
goto block_8;
}
}
else
{
lean_object* x_421; uint8_t x_422; uint8_t x_445; 
x_421 = l_Lean_Syntax_getArg(x_378, x_29);
lean_dec(x_378);
lean_inc(x_421);
x_445 = l_Lean_Syntax_isOfKind(x_421, x_307);
if (x_445 == 0)
{
uint8_t x_446; 
lean_dec(x_421);
x_446 = 0;
x_422 = x_446;
goto block_444;
}
else
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_447 = l_Lean_Syntax_getArgs(x_421);
lean_dec(x_421);
x_448 = lean_array_get_size(x_447);
lean_dec(x_447);
x_449 = lean_nat_dec_eq(x_448, x_51);
lean_dec(x_448);
x_422 = x_449;
goto block_444;
}
block_444:
{
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_399);
lean_dec(x_336);
lean_dec(x_117);
lean_dec(x_73);
x_423 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = l_Lean_Elab_Term_getEnv___rarg(x_424);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = !lean_is_exclusive(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_426, 5);
x_429 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_428);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
lean_ctor_set(x_426, 5, x_431);
x_5 = x_430;
x_6 = x_426;
goto block_8;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_432 = lean_ctor_get(x_426, 0);
x_433 = lean_ctor_get(x_426, 1);
x_434 = lean_ctor_get(x_426, 2);
x_435 = lean_ctor_get(x_426, 3);
x_436 = lean_ctor_get(x_426, 4);
x_437 = lean_ctor_get(x_426, 5);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_426);
x_438 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_437);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_441, 0, x_432);
lean_ctor_set(x_441, 1, x_433);
lean_ctor_set(x_441, 2, x_434);
lean_ctor_set(x_441, 3, x_435);
lean_ctor_set(x_441, 4, x_436);
lean_ctor_set(x_441, 5, x_440);
x_5 = x_439;
x_6 = x_441;
goto block_8;
}
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = l_Lean_Syntax_getArg(x_336, x_74);
lean_dec(x_336);
x_443 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_73, x_399, x_117, x_442, x_2, x_3, x_4);
return x_443;
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
block_857:
{
if (x_492 == 0)
{
if (x_491 == 0)
{
uint8_t x_493; 
x_493 = 0;
x_76 = x_493;
goto block_489;
}
else
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = l_Lean_Syntax_getArgs(x_75);
x_495 = lean_array_get_size(x_494);
lean_dec(x_494);
x_496 = lean_nat_dec_eq(x_495, x_29);
lean_dec(x_495);
x_76 = x_496;
goto block_489;
}
}
else
{
lean_object* x_497; lean_object* x_498; uint8_t x_499; uint8_t x_683; uint8_t x_684; 
lean_dec(x_75);
x_497 = lean_unsigned_to_nat(4u);
x_498 = l_Lean_Syntax_getArg(x_1, x_497);
lean_inc(x_498);
x_683 = l_Lean_Syntax_isOfKind(x_498, x_490);
if (x_683 == 0)
{
uint8_t x_853; 
x_853 = 0;
x_684 = x_853;
goto block_852;
}
else
{
lean_object* x_854; lean_object* x_855; uint8_t x_856; 
x_854 = l_Lean_Syntax_getArgs(x_498);
x_855 = lean_array_get_size(x_854);
lean_dec(x_854);
x_856 = lean_nat_dec_eq(x_855, x_51);
lean_dec(x_855);
x_684 = x_856;
goto block_852;
}
block_682:
{
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
lean_dec(x_73);
x_500 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_501 = lean_ctor_get(x_500, 1);
lean_inc(x_501);
lean_dec(x_500);
x_502 = l_Lean_Elab_Term_getEnv___rarg(x_501);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec(x_502);
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_505 = lean_ctor_get(x_503, 5);
x_506 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
lean_ctor_set(x_503, 5, x_508);
x_5 = x_507;
x_6 = x_503;
goto block_8;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_509 = lean_ctor_get(x_503, 0);
x_510 = lean_ctor_get(x_503, 1);
x_511 = lean_ctor_get(x_503, 2);
x_512 = lean_ctor_get(x_503, 3);
x_513 = lean_ctor_get(x_503, 4);
x_514 = lean_ctor_get(x_503, 5);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_511);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_503);
x_515 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_514);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_518, 0, x_509);
lean_ctor_set(x_518, 1, x_510);
lean_ctor_set(x_518, 2, x_511);
lean_ctor_set(x_518, 3, x_512);
lean_ctor_set(x_518, 4, x_513);
lean_ctor_set(x_518, 5, x_517);
x_5 = x_516;
x_6 = x_518;
goto block_8;
}
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; uint8_t x_677; 
x_519 = lean_unsigned_to_nat(5u);
x_520 = l_Lean_Syntax_getArg(x_1, x_519);
lean_inc(x_520);
x_677 = l_Lean_Syntax_isOfKind(x_520, x_490);
if (x_677 == 0)
{
uint8_t x_678; 
x_678 = 0;
x_521 = x_678;
goto block_676;
}
else
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_679 = l_Lean_Syntax_getArgs(x_520);
x_680 = lean_array_get_size(x_679);
lean_dec(x_679);
x_681 = lean_nat_dec_eq(x_680, x_29);
lean_dec(x_680);
x_521 = x_681;
goto block_676;
}
block_676:
{
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; 
lean_dec(x_520);
lean_dec(x_73);
x_522 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_523 = lean_ctor_get(x_522, 1);
lean_inc(x_523);
lean_dec(x_522);
x_524 = l_Lean_Elab_Term_getEnv___rarg(x_523);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_526 = !lean_is_exclusive(x_525);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_525, 5);
x_528 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_527);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
lean_ctor_set(x_525, 5, x_530);
x_5 = x_529;
x_6 = x_525;
goto block_8;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_531 = lean_ctor_get(x_525, 0);
x_532 = lean_ctor_get(x_525, 1);
x_533 = lean_ctor_get(x_525, 2);
x_534 = lean_ctor_get(x_525, 3);
x_535 = lean_ctor_get(x_525, 4);
x_536 = lean_ctor_get(x_525, 5);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_525);
x_537 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_536);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_540, 0, x_531);
lean_ctor_set(x_540, 1, x_532);
lean_ctor_set(x_540, 2, x_533);
lean_ctor_set(x_540, 3, x_534);
lean_ctor_set(x_540, 4, x_535);
lean_ctor_set(x_540, 5, x_539);
x_5 = x_538;
x_6 = x_540;
goto block_8;
}
}
else
{
lean_object* x_541; uint8_t x_542; lean_object* x_669; uint8_t x_670; 
x_541 = l_Lean_Syntax_getArg(x_520, x_51);
lean_dec(x_520);
x_669 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_541);
x_670 = l_Lean_Syntax_isOfKind(x_541, x_669);
if (x_670 == 0)
{
uint8_t x_671; 
x_671 = 0;
x_542 = x_671;
goto block_668;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
x_672 = l_Lean_Syntax_getArgs(x_541);
x_673 = lean_array_get_size(x_672);
lean_dec(x_672);
x_674 = lean_unsigned_to_nat(3u);
x_675 = lean_nat_dec_eq(x_673, x_674);
lean_dec(x_673);
x_542 = x_675;
goto block_668;
}
block_668:
{
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; 
lean_dec(x_541);
lean_dec(x_73);
x_543 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
lean_dec(x_543);
x_545 = l_Lean_Elab_Term_getEnv___rarg(x_544);
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
lean_dec(x_545);
x_547 = !lean_is_exclusive(x_546);
if (x_547 == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_548 = lean_ctor_get(x_546, 5);
x_549 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_548);
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
lean_ctor_set(x_546, 5, x_551);
x_5 = x_550;
x_6 = x_546;
goto block_8;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_552 = lean_ctor_get(x_546, 0);
x_553 = lean_ctor_get(x_546, 1);
x_554 = lean_ctor_get(x_546, 2);
x_555 = lean_ctor_get(x_546, 3);
x_556 = lean_ctor_get(x_546, 4);
x_557 = lean_ctor_get(x_546, 5);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_546);
x_558 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_557);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_561, 0, x_552);
lean_ctor_set(x_561, 1, x_553);
lean_ctor_set(x_561, 2, x_554);
lean_ctor_set(x_561, 3, x_555);
lean_ctor_set(x_561, 4, x_556);
lean_ctor_set(x_561, 5, x_560);
x_5 = x_559;
x_6 = x_561;
goto block_8;
}
}
else
{
lean_object* x_562; uint8_t x_563; uint8_t x_663; 
x_562 = l_Lean_Syntax_getArg(x_541, x_51);
lean_inc(x_562);
x_663 = l_Lean_Syntax_isOfKind(x_562, x_490);
if (x_663 == 0)
{
uint8_t x_664; 
x_664 = 0;
x_563 = x_664;
goto block_662;
}
else
{
lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_665 = l_Lean_Syntax_getArgs(x_562);
x_666 = lean_array_get_size(x_665);
lean_dec(x_665);
x_667 = lean_nat_dec_eq(x_666, x_29);
lean_dec(x_666);
x_563 = x_667;
goto block_662;
}
block_662:
{
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; 
lean_dec(x_562);
lean_dec(x_541);
lean_dec(x_73);
x_564 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_566 = l_Lean_Elab_Term_getEnv___rarg(x_565);
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = !lean_is_exclusive(x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_569 = lean_ctor_get(x_567, 5);
x_570 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_569);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
lean_ctor_set(x_567, 5, x_572);
x_5 = x_571;
x_6 = x_567;
goto block_8;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_573 = lean_ctor_get(x_567, 0);
x_574 = lean_ctor_get(x_567, 1);
x_575 = lean_ctor_get(x_567, 2);
x_576 = lean_ctor_get(x_567, 3);
x_577 = lean_ctor_get(x_567, 4);
x_578 = lean_ctor_get(x_567, 5);
lean_inc(x_578);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_567);
x_579 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_582, 0, x_573);
lean_ctor_set(x_582, 1, x_574);
lean_ctor_set(x_582, 2, x_575);
lean_ctor_set(x_582, 3, x_576);
lean_ctor_set(x_582, 4, x_577);
lean_ctor_set(x_582, 5, x_581);
x_5 = x_580;
x_6 = x_582;
goto block_8;
}
}
else
{
lean_object* x_583; uint8_t x_584; lean_object* x_656; uint8_t x_657; 
x_583 = l_Lean_Syntax_getArg(x_562, x_51);
lean_dec(x_562);
x_656 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_583);
x_657 = l_Lean_Syntax_isOfKind(x_583, x_656);
if (x_657 == 0)
{
uint8_t x_658; 
x_658 = 0;
x_584 = x_658;
goto block_655;
}
else
{
lean_object* x_659; lean_object* x_660; uint8_t x_661; 
x_659 = l_Lean_Syntax_getArgs(x_583);
x_660 = lean_array_get_size(x_659);
lean_dec(x_659);
x_661 = lean_nat_dec_eq(x_660, x_74);
lean_dec(x_660);
x_584 = x_661;
goto block_655;
}
block_655:
{
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
lean_dec(x_583);
lean_dec(x_541);
lean_dec(x_73);
x_585 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
lean_dec(x_585);
x_587 = l_Lean_Elab_Term_getEnv___rarg(x_586);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
lean_dec(x_587);
x_589 = !lean_is_exclusive(x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_590 = lean_ctor_get(x_588, 5);
x_591 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_590);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
lean_ctor_set(x_588, 5, x_593);
x_5 = x_592;
x_6 = x_588;
goto block_8;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_594 = lean_ctor_get(x_588, 0);
x_595 = lean_ctor_get(x_588, 1);
x_596 = lean_ctor_get(x_588, 2);
x_597 = lean_ctor_get(x_588, 3);
x_598 = lean_ctor_get(x_588, 4);
x_599 = lean_ctor_get(x_588, 5);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_588);
x_600 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_599);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_603, 0, x_594);
lean_ctor_set(x_603, 1, x_595);
lean_ctor_set(x_603, 2, x_596);
lean_ctor_set(x_603, 3, x_597);
lean_ctor_set(x_603, 4, x_598);
lean_ctor_set(x_603, 5, x_602);
x_5 = x_601;
x_6 = x_603;
goto block_8;
}
}
else
{
lean_object* x_604; lean_object* x_605; uint8_t x_606; 
x_604 = l_Lean_Syntax_getArg(x_583, x_51);
x_605 = l_Lean_identKind___closed__2;
lean_inc(x_604);
x_606 = l_Lean_Syntax_isOfKind(x_604, x_605);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
lean_dec(x_604);
lean_dec(x_583);
lean_dec(x_541);
lean_dec(x_73);
x_607 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
lean_dec(x_607);
x_609 = l_Lean_Elab_Term_getEnv___rarg(x_608);
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = !lean_is_exclusive(x_610);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_612 = lean_ctor_get(x_610, 5);
x_613 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_612);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
lean_ctor_set(x_610, 5, x_615);
x_5 = x_614;
x_6 = x_610;
goto block_8;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_616 = lean_ctor_get(x_610, 0);
x_617 = lean_ctor_get(x_610, 1);
x_618 = lean_ctor_get(x_610, 2);
x_619 = lean_ctor_get(x_610, 3);
x_620 = lean_ctor_get(x_610, 4);
x_621 = lean_ctor_get(x_610, 5);
lean_inc(x_621);
lean_inc(x_620);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_610);
x_622 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_621);
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
x_625 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_625, 0, x_616);
lean_ctor_set(x_625, 1, x_617);
lean_ctor_set(x_625, 2, x_618);
lean_ctor_set(x_625, 3, x_619);
lean_ctor_set(x_625, 4, x_620);
lean_ctor_set(x_625, 5, x_624);
x_5 = x_623;
x_6 = x_625;
goto block_8;
}
}
else
{
lean_object* x_626; uint8_t x_627; uint8_t x_650; 
x_626 = l_Lean_Syntax_getArg(x_583, x_29);
lean_dec(x_583);
lean_inc(x_626);
x_650 = l_Lean_Syntax_isOfKind(x_626, x_490);
if (x_650 == 0)
{
uint8_t x_651; 
lean_dec(x_626);
x_651 = 0;
x_627 = x_651;
goto block_649;
}
else
{
lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_652 = l_Lean_Syntax_getArgs(x_626);
lean_dec(x_626);
x_653 = lean_array_get_size(x_652);
lean_dec(x_652);
x_654 = lean_nat_dec_eq(x_653, x_51);
lean_dec(x_653);
x_627 = x_654;
goto block_649;
}
block_649:
{
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
lean_dec(x_604);
lean_dec(x_541);
lean_dec(x_73);
x_628 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_629 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
lean_dec(x_628);
x_630 = l_Lean_Elab_Term_getEnv___rarg(x_629);
x_631 = lean_ctor_get(x_630, 1);
lean_inc(x_631);
lean_dec(x_630);
x_632 = !lean_is_exclusive(x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_631, 5);
x_634 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_633);
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
lean_ctor_set(x_631, 5, x_636);
x_5 = x_635;
x_6 = x_631;
goto block_8;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_637 = lean_ctor_get(x_631, 0);
x_638 = lean_ctor_get(x_631, 1);
x_639 = lean_ctor_get(x_631, 2);
x_640 = lean_ctor_get(x_631, 3);
x_641 = lean_ctor_get(x_631, 4);
x_642 = lean_ctor_get(x_631, 5);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_631);
x_643 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_642);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_646, 0, x_637);
lean_ctor_set(x_646, 1, x_638);
lean_ctor_set(x_646, 2, x_639);
lean_ctor_set(x_646, 3, x_640);
lean_ctor_set(x_646, 4, x_641);
lean_ctor_set(x_646, 5, x_645);
x_5 = x_644;
x_6 = x_646;
goto block_8;
}
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = l_Lean_Syntax_getArg(x_541, x_74);
lean_dec(x_541);
x_648 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_73, x_604, x_647, x_2, x_3, x_4);
return x_648;
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
block_852:
{
if (x_684 == 0)
{
if (x_683 == 0)
{
uint8_t x_685; 
lean_dec(x_498);
x_685 = 0;
x_499 = x_685;
goto block_682;
}
else
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_686 = l_Lean_Syntax_getArgs(x_498);
lean_dec(x_498);
x_687 = lean_array_get_size(x_686);
lean_dec(x_686);
x_688 = lean_nat_dec_eq(x_687, x_29);
lean_dec(x_687);
x_499 = x_688;
goto block_682;
}
}
else
{
lean_object* x_689; lean_object* x_690; uint8_t x_691; uint8_t x_847; 
lean_dec(x_498);
x_689 = lean_unsigned_to_nat(5u);
x_690 = l_Lean_Syntax_getArg(x_1, x_689);
lean_inc(x_690);
x_847 = l_Lean_Syntax_isOfKind(x_690, x_490);
if (x_847 == 0)
{
uint8_t x_848; 
x_848 = 0;
x_691 = x_848;
goto block_846;
}
else
{
lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_849 = l_Lean_Syntax_getArgs(x_690);
x_850 = lean_array_get_size(x_849);
lean_dec(x_849);
x_851 = lean_nat_dec_eq(x_850, x_29);
lean_dec(x_850);
x_691 = x_851;
goto block_846;
}
block_846:
{
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; 
lean_dec(x_690);
lean_dec(x_73);
x_692 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_693 = lean_ctor_get(x_692, 1);
lean_inc(x_693);
lean_dec(x_692);
x_694 = l_Lean_Elab_Term_getEnv___rarg(x_693);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
lean_dec(x_694);
x_696 = !lean_is_exclusive(x_695);
if (x_696 == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_697 = lean_ctor_get(x_695, 5);
x_698 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_697);
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
lean_ctor_set(x_695, 5, x_700);
x_5 = x_699;
x_6 = x_695;
goto block_8;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_701 = lean_ctor_get(x_695, 0);
x_702 = lean_ctor_get(x_695, 1);
x_703 = lean_ctor_get(x_695, 2);
x_704 = lean_ctor_get(x_695, 3);
x_705 = lean_ctor_get(x_695, 4);
x_706 = lean_ctor_get(x_695, 5);
lean_inc(x_706);
lean_inc(x_705);
lean_inc(x_704);
lean_inc(x_703);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_695);
x_707 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_706);
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_710, 0, x_701);
lean_ctor_set(x_710, 1, x_702);
lean_ctor_set(x_710, 2, x_703);
lean_ctor_set(x_710, 3, x_704);
lean_ctor_set(x_710, 4, x_705);
lean_ctor_set(x_710, 5, x_709);
x_5 = x_708;
x_6 = x_710;
goto block_8;
}
}
else
{
lean_object* x_711; uint8_t x_712; lean_object* x_839; uint8_t x_840; 
x_711 = l_Lean_Syntax_getArg(x_690, x_51);
lean_dec(x_690);
x_839 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_711);
x_840 = l_Lean_Syntax_isOfKind(x_711, x_839);
if (x_840 == 0)
{
uint8_t x_841; 
x_841 = 0;
x_712 = x_841;
goto block_838;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; uint8_t x_845; 
x_842 = l_Lean_Syntax_getArgs(x_711);
x_843 = lean_array_get_size(x_842);
lean_dec(x_842);
x_844 = lean_unsigned_to_nat(3u);
x_845 = lean_nat_dec_eq(x_843, x_844);
lean_dec(x_843);
x_712 = x_845;
goto block_838;
}
block_838:
{
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; 
lean_dec(x_711);
lean_dec(x_73);
x_713 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_714 = lean_ctor_get(x_713, 1);
lean_inc(x_714);
lean_dec(x_713);
x_715 = l_Lean_Elab_Term_getEnv___rarg(x_714);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
lean_dec(x_715);
x_717 = !lean_is_exclusive(x_716);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_718 = lean_ctor_get(x_716, 5);
x_719 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
lean_ctor_set(x_716, 5, x_721);
x_5 = x_720;
x_6 = x_716;
goto block_8;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_722 = lean_ctor_get(x_716, 0);
x_723 = lean_ctor_get(x_716, 1);
x_724 = lean_ctor_get(x_716, 2);
x_725 = lean_ctor_get(x_716, 3);
x_726 = lean_ctor_get(x_716, 4);
x_727 = lean_ctor_get(x_716, 5);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_724);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_716);
x_728 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_727);
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
x_731 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_731, 0, x_722);
lean_ctor_set(x_731, 1, x_723);
lean_ctor_set(x_731, 2, x_724);
lean_ctor_set(x_731, 3, x_725);
lean_ctor_set(x_731, 4, x_726);
lean_ctor_set(x_731, 5, x_730);
x_5 = x_729;
x_6 = x_731;
goto block_8;
}
}
else
{
lean_object* x_732; uint8_t x_733; uint8_t x_833; 
x_732 = l_Lean_Syntax_getArg(x_711, x_51);
lean_inc(x_732);
x_833 = l_Lean_Syntax_isOfKind(x_732, x_490);
if (x_833 == 0)
{
uint8_t x_834; 
x_834 = 0;
x_733 = x_834;
goto block_832;
}
else
{
lean_object* x_835; lean_object* x_836; uint8_t x_837; 
x_835 = l_Lean_Syntax_getArgs(x_732);
x_836 = lean_array_get_size(x_835);
lean_dec(x_835);
x_837 = lean_nat_dec_eq(x_836, x_29);
lean_dec(x_836);
x_733 = x_837;
goto block_832;
}
block_832:
{
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
lean_dec(x_732);
lean_dec(x_711);
lean_dec(x_73);
x_734 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_735 = lean_ctor_get(x_734, 1);
lean_inc(x_735);
lean_dec(x_734);
x_736 = l_Lean_Elab_Term_getEnv___rarg(x_735);
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec(x_736);
x_738 = !lean_is_exclusive(x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_739 = lean_ctor_get(x_737, 5);
x_740 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_739);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
lean_ctor_set(x_737, 5, x_742);
x_5 = x_741;
x_6 = x_737;
goto block_8;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_743 = lean_ctor_get(x_737, 0);
x_744 = lean_ctor_get(x_737, 1);
x_745 = lean_ctor_get(x_737, 2);
x_746 = lean_ctor_get(x_737, 3);
x_747 = lean_ctor_get(x_737, 4);
x_748 = lean_ctor_get(x_737, 5);
lean_inc(x_748);
lean_inc(x_747);
lean_inc(x_746);
lean_inc(x_745);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_737);
x_749 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_748);
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec(x_749);
x_752 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_752, 0, x_743);
lean_ctor_set(x_752, 1, x_744);
lean_ctor_set(x_752, 2, x_745);
lean_ctor_set(x_752, 3, x_746);
lean_ctor_set(x_752, 4, x_747);
lean_ctor_set(x_752, 5, x_751);
x_5 = x_750;
x_6 = x_752;
goto block_8;
}
}
else
{
lean_object* x_753; uint8_t x_754; lean_object* x_826; uint8_t x_827; 
x_753 = l_Lean_Syntax_getArg(x_732, x_51);
lean_dec(x_732);
x_826 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_753);
x_827 = l_Lean_Syntax_isOfKind(x_753, x_826);
if (x_827 == 0)
{
uint8_t x_828; 
x_828 = 0;
x_754 = x_828;
goto block_825;
}
else
{
lean_object* x_829; lean_object* x_830; uint8_t x_831; 
x_829 = l_Lean_Syntax_getArgs(x_753);
x_830 = lean_array_get_size(x_829);
lean_dec(x_829);
x_831 = lean_nat_dec_eq(x_830, x_74);
lean_dec(x_830);
x_754 = x_831;
goto block_825;
}
block_825:
{
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; 
lean_dec(x_753);
lean_dec(x_711);
lean_dec(x_73);
x_755 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_756 = lean_ctor_get(x_755, 1);
lean_inc(x_756);
lean_dec(x_755);
x_757 = l_Lean_Elab_Term_getEnv___rarg(x_756);
x_758 = lean_ctor_get(x_757, 1);
lean_inc(x_758);
lean_dec(x_757);
x_759 = !lean_is_exclusive(x_758);
if (x_759 == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_760 = lean_ctor_get(x_758, 5);
x_761 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_760);
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
lean_ctor_set(x_758, 5, x_763);
x_5 = x_762;
x_6 = x_758;
goto block_8;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_764 = lean_ctor_get(x_758, 0);
x_765 = lean_ctor_get(x_758, 1);
x_766 = lean_ctor_get(x_758, 2);
x_767 = lean_ctor_get(x_758, 3);
x_768 = lean_ctor_get(x_758, 4);
x_769 = lean_ctor_get(x_758, 5);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_758);
x_770 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_769);
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
x_773 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_773, 0, x_764);
lean_ctor_set(x_773, 1, x_765);
lean_ctor_set(x_773, 2, x_766);
lean_ctor_set(x_773, 3, x_767);
lean_ctor_set(x_773, 4, x_768);
lean_ctor_set(x_773, 5, x_772);
x_5 = x_771;
x_6 = x_773;
goto block_8;
}
}
else
{
lean_object* x_774; lean_object* x_775; uint8_t x_776; 
x_774 = l_Lean_Syntax_getArg(x_753, x_51);
x_775 = l_Lean_identKind___closed__2;
lean_inc(x_774);
x_776 = l_Lean_Syntax_isOfKind(x_774, x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; 
lean_dec(x_774);
lean_dec(x_753);
lean_dec(x_711);
lean_dec(x_73);
x_777 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_778 = lean_ctor_get(x_777, 1);
lean_inc(x_778);
lean_dec(x_777);
x_779 = l_Lean_Elab_Term_getEnv___rarg(x_778);
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
lean_dec(x_779);
x_781 = !lean_is_exclusive(x_780);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = lean_ctor_get(x_780, 5);
x_783 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_782);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
lean_ctor_set(x_780, 5, x_785);
x_5 = x_784;
x_6 = x_780;
goto block_8;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_786 = lean_ctor_get(x_780, 0);
x_787 = lean_ctor_get(x_780, 1);
x_788 = lean_ctor_get(x_780, 2);
x_789 = lean_ctor_get(x_780, 3);
x_790 = lean_ctor_get(x_780, 4);
x_791 = lean_ctor_get(x_780, 5);
lean_inc(x_791);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_780);
x_792 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_791);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_795, 0, x_786);
lean_ctor_set(x_795, 1, x_787);
lean_ctor_set(x_795, 2, x_788);
lean_ctor_set(x_795, 3, x_789);
lean_ctor_set(x_795, 4, x_790);
lean_ctor_set(x_795, 5, x_794);
x_5 = x_793;
x_6 = x_795;
goto block_8;
}
}
else
{
lean_object* x_796; uint8_t x_797; uint8_t x_820; 
x_796 = l_Lean_Syntax_getArg(x_753, x_29);
lean_dec(x_753);
lean_inc(x_796);
x_820 = l_Lean_Syntax_isOfKind(x_796, x_490);
if (x_820 == 0)
{
uint8_t x_821; 
lean_dec(x_796);
x_821 = 0;
x_797 = x_821;
goto block_819;
}
else
{
lean_object* x_822; lean_object* x_823; uint8_t x_824; 
x_822 = l_Lean_Syntax_getArgs(x_796);
lean_dec(x_796);
x_823 = lean_array_get_size(x_822);
lean_dec(x_822);
x_824 = lean_nat_dec_eq(x_823, x_51);
lean_dec(x_823);
x_797 = x_824;
goto block_819;
}
block_819:
{
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
lean_dec(x_774);
lean_dec(x_711);
lean_dec(x_73);
x_798 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_799 = lean_ctor_get(x_798, 1);
lean_inc(x_799);
lean_dec(x_798);
x_800 = l_Lean_Elab_Term_getEnv___rarg(x_799);
x_801 = lean_ctor_get(x_800, 1);
lean_inc(x_801);
lean_dec(x_800);
x_802 = !lean_is_exclusive(x_801);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_803 = lean_ctor_get(x_801, 5);
x_804 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_803);
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec(x_804);
lean_ctor_set(x_801, 5, x_806);
x_5 = x_805;
x_6 = x_801;
goto block_8;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_807 = lean_ctor_get(x_801, 0);
x_808 = lean_ctor_get(x_801, 1);
x_809 = lean_ctor_get(x_801, 2);
x_810 = lean_ctor_get(x_801, 3);
x_811 = lean_ctor_get(x_801, 4);
x_812 = lean_ctor_get(x_801, 5);
lean_inc(x_812);
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
lean_inc(x_808);
lean_inc(x_807);
lean_dec(x_801);
x_813 = l___private_Lean_Elab_Match_4__expandMatchDiscr_x3f___rarg(x_812);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec(x_813);
x_816 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_816, 0, x_807);
lean_ctor_set(x_816, 1, x_808);
lean_ctor_set(x_816, 2, x_809);
lean_ctor_set(x_816, 3, x_810);
lean_ctor_set(x_816, 4, x_811);
lean_ctor_set(x_816, 5, x_815);
x_5 = x_814;
x_6 = x_816;
goto block_8;
}
}
else
{
lean_object* x_817; lean_object* x_818; 
x_817 = l_Lean_Syntax_getArg(x_711, x_74);
lean_dec(x_711);
x_818 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_73, x_774, x_817, x_2, x_3, x_4);
return x_818;
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
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMatch), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5);
l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6 = _init_l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6);
l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1 = _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1);
l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2 = _init_l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2);
l___private_Lean_Elab_Match_3__elabMatchCore___closed__1 = _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabMatchCore___closed__1);
l___private_Lean_Elab_Match_3__elabMatchCore___closed__2 = _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabMatchCore___closed__2);
l___private_Lean_Elab_Match_3__elabMatchCore___closed__3 = _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabMatchCore___closed__3);
l___private_Lean_Elab_Match_3__elabMatchCore___closed__4 = _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabMatchCore___closed__4);
l___private_Lean_Elab_Match_3__elabMatchCore___closed__5 = _init_l___private_Lean_Elab_Match_3__elabMatchCore___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_3__elabMatchCore___closed__5);
l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
