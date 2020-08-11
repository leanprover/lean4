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
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__2(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMatch(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__1;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_5__getMatchAlts(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_FS_Handle_putStrLn___rarg___closed__1;
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___closed__5;
lean_object* l_Lean_Elab_Term_mkMatchAltView___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___closed__3;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
lean_object* l___private_Lean_Elab_Match_5__getMatchAlts___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12;
lean_object* l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacros___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__6;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___private_Lean_Elab_Match_6__elabMatchCore___spec__2(lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__3;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___closed__4;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__5;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8;
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabMatch___closed__1;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_1__expandSimpleMatch___closed__4;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkMatchAltView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_5, x_4, x_2, x_6);
lean_dec(x_4);
x_8 = l_Lean_Syntax_getArg(x_1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_mkMatchAltView___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkMatchAltView(x_1);
lean_dec(x_1);
return x_2;
}
}
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
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkHole___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_List_format___rarg___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12;
x_2 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
x_9 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_8, x_3, x_4);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Syntax_copyInfo(x_15, x_1);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14;
x_20 = lean_array_push(x_19, x_17);
x_21 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Syntax_copyInfo(x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkHole(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Syntax_isNone(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main(x_1, x_3, x_4, x_5);
return x_12;
}
}
}
lean_object* l___private_Lean_Elab_Match_4__expandMatchOptType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Elab_expandMacros___main(x_1, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_12, x_2, x_19);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_20;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; uint8_t x_22; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_21 = x_10;
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = x_23;
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_11);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getEnv___rarg(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 4);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_environment_main_module(x_32);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = x_26;
x_45 = lean_apply_2(x_44, x_43, x_38);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_31, 5);
lean_dec(x_47);
x_48 = lean_ctor_get(x_31, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_31, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_31, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_31, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_31, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
lean_ctor_set(x_31, 5, x_54);
lean_ctor_set(x_21, 0, x_53);
x_13 = x_21;
x_14 = x_31;
goto block_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_31);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_34);
lean_ctor_set(x_57, 2, x_35);
lean_ctor_set(x_57, 3, x_36);
lean_ctor_set(x_57, 4, x_37);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_21, 0, x_55);
x_13 = x_21;
x_14 = x_57;
goto block_20;
}
}
else
{
lean_object* x_58; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
lean_dec(x_45);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_Elab_Term_throwError___rarg(x_59, x_62, x_4, x_31);
lean_dec(x_59);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_4);
x_68 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_31);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = x_73;
lean_inc(x_1);
x_76 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__1), 5, 3);
lean_closure_set(x_76, 0, x_1);
lean_closure_set(x_76, 1, x_11);
lean_closure_set(x_76, 2, x_75);
x_77 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_getEnv___rarg(x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_4, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 4);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_environment_main_module(x_82);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_78);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
x_94 = x_76;
x_95 = lean_apply_2(x_94, x_93, x_88);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_84);
lean_ctor_set(x_99, 2, x_85);
lean_ctor_set(x_99, 3, x_86);
lean_ctor_set(x_99, 4, x_87);
lean_ctor_set(x_99, 5, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_74);
x_13 = x_100;
x_14 = x_99;
goto block_20;
}
else
{
lean_object* x_101; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_74);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
lean_dec(x_95);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Elab_Term_throwError___rarg(x_102, x_105, x_4, x_81);
lean_dec(x_102);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_111 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_81);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = x_13;
x_18 = lean_array_fset(x_12, x_2, x_17);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_18;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandMacrosInPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = x_1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_expandMacrosInPatterns___spec__2), 5, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
x_10 = x_9;
x_11 = lean_apply_2(x_10, x_2, x_6);
return x_11;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_Parser_Term_matchAlt___closed__2;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_Elab_Term_mkMatchAltView(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Match_5__getMatchAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__1(x_4, x_5, x_5);
x_7 = x_6;
x_8 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_5__getMatchAlts___spec__2(x_5, x_7);
x_9 = x_8;
return x_9;
}
}
lean_object* l___private_Lean_Elab_Match_5__getMatchAlts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Match_5__getMatchAlts(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(uint8_t x_1, lean_object* x_2) {
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
x_14 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(x_1, x_5);
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
x_25 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(x_20, x_18);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
}
}
lean_object* l_List_toString___at___private_Lean_Elab_Match_6__elabMatchCore___spec__2(lean_object* x_1) {
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
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_12 = l_List_toString___at___private_Lean_Elab_Match_6__elabMatchCore___spec__2(x_11);
x_13 = l_Array_HasRepr___rarg___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = x_14;
x_18 = lean_array_fset(x_8, x_1, x_17);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP type: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabMatchCore___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabMatchCore___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Handle_putStrLn___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Match_6__elabMatchCore___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
x_13 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__1(x_9, x_12);
x_14 = x_13;
x_56 = l_Lean_Syntax_getArg(x_1, x_8);
x_57 = lean_array_get_size(x_14);
x_58 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Term_getEnv___rarg(x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_64, 5);
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 4);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_environment_main_module(x_65);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
x_73 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_56, x_57, x_72, x_67);
lean_dec(x_72);
lean_dec(x_57);
lean_dec(x_56);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_ctor_set(x_64, 5, x_75);
x_15 = x_74;
x_16 = x_64;
goto block_55;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_64, 0);
x_77 = lean_ctor_get(x_64, 1);
x_78 = lean_ctor_get(x_64, 2);
x_79 = lean_ctor_get(x_64, 3);
x_80 = lean_ctor_get(x_64, 4);
x_81 = lean_ctor_get(x_64, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_64);
x_82 = lean_ctor_get(x_3, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 4);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_environment_main_module(x_65);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_61);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
x_87 = l___private_Lean_Elab_Match_4__expandMatchOptType(x_1, x_56, x_57, x_86, x_81);
lean_dec(x_86);
lean_dec(x_57);
lean_dec(x_56);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_77);
lean_ctor_set(x_90, 2, x_78);
lean_ctor_set(x_90, 3, x_79);
lean_ctor_set(x_90, 4, x_80);
lean_ctor_set(x_90, 5, x_89);
x_15 = x_88;
x_16 = x_90;
goto block_55;
}
}
else
{
uint8_t x_91; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_14);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_58);
if (x_91 == 0)
{
return x_58;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_58, 0);
x_93 = lean_ctor_get(x_58, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_58);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_55:
{
lean_object* x_17; 
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_elabType(x_15, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_Match_5__getMatchAlts(x_1);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_expandMacrosInPatterns(x_20, x_3, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = l___private_Lean_Elab_Match_6__elabMatchCore___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Elab_Match_6__elabMatchCore___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
x_30 = l_List_toString___at___private_Lean_Elab_Match_6__elabMatchCore___spec__2(x_29);
x_31 = l_Array_HasRepr___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
x_37 = x_22;
x_38 = l_Array_umapMAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__4(x_9, x_37);
x_39 = x_38;
x_40 = l_Array_toList___rarg(x_39);
lean_dec(x_39);
x_41 = l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(x_40);
x_42 = lean_string_append(x_31, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Term_throwError___rarg(x_1, x_45, x_3, x_23);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
lean_object* l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at___private_Lean_Elab_Match_6__elabMatchCore___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Match_6__elabMatchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Match_6__elabMatchCore(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg), 1, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_9; lean_object* x_906; uint8_t x_907; 
x_906 = l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_inc(x_1);
x_907 = l_Lean_Syntax_isOfKind(x_1, x_906);
if (x_907 == 0)
{
uint8_t x_908; 
x_908 = 0;
x_9 = x_908;
goto block_905;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; 
x_909 = l_Lean_Syntax_getArgs(x_1);
x_910 = lean_array_get_size(x_909);
lean_dec(x_909);
x_911 = lean_unsigned_to_nat(6u);
x_912 = lean_nat_dec_eq(x_910, x_911);
lean_dec(x_910);
x_9 = x_912;
goto block_905;
}
block_8:
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l___private_Lean_Elab_Match_6__elabMatchCore(x_1, x_2, x_3, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
block_905:
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
x_16 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_15);
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
x_25 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_24);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_899; uint8_t x_900; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_899 = l_Lean_nullKind___closed__2;
lean_inc(x_30);
x_900 = l_Lean_Syntax_isOfKind(x_30, x_899);
if (x_900 == 0)
{
uint8_t x_901; 
x_901 = 0;
x_31 = x_901;
goto block_898;
}
else
{
lean_object* x_902; lean_object* x_903; uint8_t x_904; 
x_902 = l_Lean_Syntax_getArgs(x_30);
x_903 = lean_array_get_size(x_902);
lean_dec(x_902);
x_904 = lean_nat_dec_eq(x_903, x_29);
lean_dec(x_903);
x_31 = x_904;
goto block_898;
}
block_898:
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
x_38 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_37);
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
x_47 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_46);
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
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_891; uint8_t x_892; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_30, x_51);
lean_dec(x_30);
x_891 = l_Lean_Parser_Term_matchDiscr___elambda__1___closed__2;
lean_inc(x_52);
x_892 = l_Lean_Syntax_isOfKind(x_52, x_891);
if (x_892 == 0)
{
uint8_t x_893; 
x_893 = 0;
x_53 = x_893;
goto block_890;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; uint8_t x_897; 
x_894 = l_Lean_Syntax_getArgs(x_52);
x_895 = lean_array_get_size(x_894);
lean_dec(x_894);
x_896 = lean_unsigned_to_nat(2u);
x_897 = lean_nat_dec_eq(x_895, x_896);
lean_dec(x_895);
x_53 = x_897;
goto block_890;
}
block_890:
{
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_52);
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
x_60 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_59);
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
x_69 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_68);
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
lean_object* x_73; uint8_t x_74; lean_object* x_884; uint8_t x_885; 
x_73 = l_Lean_Syntax_getArg(x_52, x_51);
x_884 = l_Lean_nullKind___closed__2;
lean_inc(x_73);
x_885 = l_Lean_Syntax_isOfKind(x_73, x_884);
if (x_885 == 0)
{
uint8_t x_886; 
lean_dec(x_73);
x_886 = 0;
x_74 = x_886;
goto block_883;
}
else
{
lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_887 = l_Lean_Syntax_getArgs(x_73);
lean_dec(x_73);
x_888 = lean_array_get_size(x_887);
lean_dec(x_887);
x_889 = lean_nat_dec_eq(x_888, x_51);
lean_dec(x_888);
x_74 = x_889;
goto block_883;
}
block_883:
{
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_52);
x_75 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Elab_Term_getEnv___rarg(x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_78, 5);
x_81 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_ctor_set(x_78, 5, x_83);
x_5 = x_82;
x_6 = x_78;
goto block_8;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_78, 0);
x_85 = lean_ctor_get(x_78, 1);
x_86 = lean_ctor_get(x_78, 2);
x_87 = lean_ctor_get(x_78, 3);
x_88 = lean_ctor_get(x_78, 4);
x_89 = lean_ctor_get(x_78, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_78);
x_90 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_87);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_92);
x_5 = x_91;
x_6 = x_93;
goto block_8;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_511; uint8_t x_512; uint8_t x_513; 
x_94 = l_Lean_Syntax_getArg(x_52, x_29);
lean_dec(x_52);
x_95 = lean_unsigned_to_nat(2u);
x_96 = l_Lean_Syntax_getArg(x_1, x_95);
x_511 = l_Lean_nullKind___closed__2;
lean_inc(x_96);
x_512 = l_Lean_Syntax_isOfKind(x_96, x_511);
if (x_512 == 0)
{
uint8_t x_879; 
x_879 = 0;
x_513 = x_879;
goto block_878;
}
else
{
lean_object* x_880; lean_object* x_881; uint8_t x_882; 
x_880 = l_Lean_Syntax_getArgs(x_96);
x_881 = lean_array_get_size(x_880);
lean_dec(x_880);
x_882 = lean_nat_dec_eq(x_881, x_51);
lean_dec(x_881);
x_513 = x_882;
goto block_878;
}
block_510:
{
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_96);
lean_dec(x_94);
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
x_104 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_103);
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
x_113 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_112);
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
lean_object* x_117; uint8_t x_118; lean_object* x_504; uint8_t x_505; 
x_117 = l_Lean_Syntax_getArg(x_96, x_51);
lean_dec(x_96);
x_504 = l_Lean_Parser_Term_typeSpec___elambda__1___closed__2;
lean_inc(x_117);
x_505 = l_Lean_Syntax_isOfKind(x_117, x_504);
if (x_505 == 0)
{
uint8_t x_506; 
x_506 = 0;
x_118 = x_506;
goto block_503;
}
else
{
lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_507 = l_Lean_Syntax_getArgs(x_117);
x_508 = lean_array_get_size(x_507);
lean_dec(x_507);
x_509 = lean_nat_dec_eq(x_508, x_95);
lean_dec(x_508);
x_118 = x_509;
goto block_503;
}
block_503:
{
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_117);
lean_dec(x_94);
x_119 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Lean_Elab_Term_getEnv___rarg(x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_122, 5);
x_125 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_ctor_set(x_122, 5, x_127);
x_5 = x_126;
x_6 = x_122;
goto block_8;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
x_130 = lean_ctor_get(x_122, 2);
x_131 = lean_ctor_get(x_122, 3);
x_132 = lean_ctor_get(x_122, 4);
x_133 = lean_ctor_get(x_122, 5);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
x_134 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_130);
lean_ctor_set(x_137, 3, x_131);
lean_ctor_set(x_137, 4, x_132);
lean_ctor_set(x_137, 5, x_136);
x_5 = x_135;
x_6 = x_137;
goto block_8;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_328; uint8_t x_329; uint8_t x_330; 
x_138 = l_Lean_Syntax_getArg(x_117, x_29);
lean_dec(x_117);
x_139 = lean_unsigned_to_nat(4u);
x_140 = l_Lean_Syntax_getArg(x_1, x_139);
x_328 = l_Lean_nullKind___closed__2;
lean_inc(x_140);
x_329 = l_Lean_Syntax_isOfKind(x_140, x_328);
if (x_329 == 0)
{
uint8_t x_499; 
x_499 = 0;
x_330 = x_499;
goto block_498;
}
else
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_500 = l_Lean_Syntax_getArgs(x_140);
x_501 = lean_array_get_size(x_500);
lean_dec(x_500);
x_502 = lean_nat_dec_eq(x_501, x_51);
lean_dec(x_501);
x_330 = x_502;
goto block_498;
}
block_327:
{
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_138);
lean_dec(x_94);
x_142 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Lean_Elab_Term_getEnv___rarg(x_143);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_145, 5);
x_148 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_ctor_set(x_145, 5, x_150);
x_5 = x_149;
x_6 = x_145;
goto block_8;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_151 = lean_ctor_get(x_145, 0);
x_152 = lean_ctor_get(x_145, 1);
x_153 = lean_ctor_get(x_145, 2);
x_154 = lean_ctor_get(x_145, 3);
x_155 = lean_ctor_get(x_145, 4);
x_156 = lean_ctor_get(x_145, 5);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_145);
x_157 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_152);
lean_ctor_set(x_160, 2, x_153);
lean_ctor_set(x_160, 3, x_154);
lean_ctor_set(x_160, 4, x_155);
lean_ctor_set(x_160, 5, x_159);
x_5 = x_158;
x_6 = x_160;
goto block_8;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_321; uint8_t x_322; 
x_161 = lean_unsigned_to_nat(5u);
x_162 = l_Lean_Syntax_getArg(x_1, x_161);
x_321 = l_Lean_nullKind___closed__2;
lean_inc(x_162);
x_322 = l_Lean_Syntax_isOfKind(x_162, x_321);
if (x_322 == 0)
{
uint8_t x_323; 
x_323 = 0;
x_163 = x_323;
goto block_320;
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = l_Lean_Syntax_getArgs(x_162);
x_325 = lean_array_get_size(x_324);
lean_dec(x_324);
x_326 = lean_nat_dec_eq(x_325, x_29);
lean_dec(x_325);
x_163 = x_326;
goto block_320;
}
block_320:
{
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_162);
lean_dec(x_138);
lean_dec(x_94);
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
x_170 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_169);
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
x_179 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_178);
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
lean_object* x_183; uint8_t x_184; lean_object* x_313; uint8_t x_314; 
x_183 = l_Lean_Syntax_getArg(x_162, x_51);
lean_dec(x_162);
x_313 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_183);
x_314 = l_Lean_Syntax_isOfKind(x_183, x_313);
if (x_314 == 0)
{
uint8_t x_315; 
x_315 = 0;
x_184 = x_315;
goto block_312;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = l_Lean_Syntax_getArgs(x_183);
x_317 = lean_array_get_size(x_316);
lean_dec(x_316);
x_318 = lean_unsigned_to_nat(3u);
x_319 = lean_nat_dec_eq(x_317, x_318);
lean_dec(x_317);
x_184 = x_319;
goto block_312;
}
block_312:
{
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_183);
lean_dec(x_138);
lean_dec(x_94);
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
x_191 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_190);
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
x_200 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_199);
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
lean_object* x_204; uint8_t x_205; lean_object* x_306; uint8_t x_307; 
x_204 = l_Lean_Syntax_getArg(x_183, x_51);
x_306 = l_Lean_nullKind___closed__2;
lean_inc(x_204);
x_307 = l_Lean_Syntax_isOfKind(x_204, x_306);
if (x_307 == 0)
{
uint8_t x_308; 
x_308 = 0;
x_205 = x_308;
goto block_305;
}
else
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = l_Lean_Syntax_getArgs(x_204);
x_310 = lean_array_get_size(x_309);
lean_dec(x_309);
x_311 = lean_nat_dec_eq(x_310, x_29);
lean_dec(x_310);
x_205 = x_311;
goto block_305;
}
block_305:
{
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_204);
lean_dec(x_183);
lean_dec(x_138);
lean_dec(x_94);
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
x_212 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_211);
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
x_221 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_220);
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
lean_object* x_225; uint8_t x_226; lean_object* x_299; uint8_t x_300; 
x_225 = l_Lean_Syntax_getArg(x_204, x_51);
lean_dec(x_204);
x_299 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_225);
x_300 = l_Lean_Syntax_isOfKind(x_225, x_299);
if (x_300 == 0)
{
uint8_t x_301; 
x_301 = 0;
x_226 = x_301;
goto block_298;
}
else
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = l_Lean_Syntax_getArgs(x_225);
x_303 = lean_array_get_size(x_302);
lean_dec(x_302);
x_304 = lean_nat_dec_eq(x_303, x_95);
lean_dec(x_303);
x_226 = x_304;
goto block_298;
}
block_298:
{
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_225);
lean_dec(x_183);
lean_dec(x_138);
lean_dec(x_94);
x_227 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Lean_Elab_Term_getEnv___rarg(x_228);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_230, 5);
x_233 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
lean_ctor_set(x_230, 5, x_235);
x_5 = x_234;
x_6 = x_230;
goto block_8;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_230, 0);
x_237 = lean_ctor_get(x_230, 1);
x_238 = lean_ctor_get(x_230, 2);
x_239 = lean_ctor_get(x_230, 3);
x_240 = lean_ctor_get(x_230, 4);
x_241 = lean_ctor_get(x_230, 5);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_230);
x_242 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_245, 0, x_236);
lean_ctor_set(x_245, 1, x_237);
lean_ctor_set(x_245, 2, x_238);
lean_ctor_set(x_245, 3, x_239);
lean_ctor_set(x_245, 4, x_240);
lean_ctor_set(x_245, 5, x_244);
x_5 = x_243;
x_6 = x_245;
goto block_8;
}
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = l_Lean_Syntax_getArg(x_225, x_51);
x_247 = l_Lean_identKind___closed__2;
lean_inc(x_246);
x_248 = l_Lean_Syntax_isOfKind(x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_246);
lean_dec(x_225);
lean_dec(x_183);
lean_dec(x_138);
lean_dec(x_94);
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
x_255 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_254);
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
x_264 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_263);
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
lean_object* x_268; uint8_t x_269; lean_object* x_292; uint8_t x_293; 
x_268 = l_Lean_Syntax_getArg(x_225, x_29);
lean_dec(x_225);
x_292 = l_Lean_nullKind___closed__2;
lean_inc(x_268);
x_293 = l_Lean_Syntax_isOfKind(x_268, x_292);
if (x_293 == 0)
{
uint8_t x_294; 
lean_dec(x_268);
x_294 = 0;
x_269 = x_294;
goto block_291;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = l_Lean_Syntax_getArgs(x_268);
lean_dec(x_268);
x_296 = lean_array_get_size(x_295);
lean_dec(x_295);
x_297 = lean_nat_dec_eq(x_296, x_51);
lean_dec(x_296);
x_269 = x_297;
goto block_291;
}
block_291:
{
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_246);
lean_dec(x_183);
lean_dec(x_138);
lean_dec(x_94);
x_270 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = l_Lean_Elab_Term_getEnv___rarg(x_271);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_273, 5);
x_276 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_ctor_set(x_273, 5, x_278);
x_5 = x_277;
x_6 = x_273;
goto block_8;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_279 = lean_ctor_get(x_273, 0);
x_280 = lean_ctor_get(x_273, 1);
x_281 = lean_ctor_get(x_273, 2);
x_282 = lean_ctor_get(x_273, 3);
x_283 = lean_ctor_get(x_273, 4);
x_284 = lean_ctor_get(x_273, 5);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_273);
x_285 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_288, 0, x_279);
lean_ctor_set(x_288, 1, x_280);
lean_ctor_set(x_288, 2, x_281);
lean_ctor_set(x_288, 3, x_282);
lean_ctor_set(x_288, 4, x_283);
lean_ctor_set(x_288, 5, x_287);
x_5 = x_286;
x_6 = x_288;
goto block_8;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = l_Lean_Syntax_getArg(x_183, x_95);
lean_dec(x_183);
x_290 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_94, x_246, x_138, x_289, x_2, x_3, x_4);
return x_290;
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
block_498:
{
if (x_330 == 0)
{
if (x_329 == 0)
{
uint8_t x_331; 
lean_dec(x_140);
x_331 = 0;
x_141 = x_331;
goto block_327;
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_332 = l_Lean_Syntax_getArgs(x_140);
lean_dec(x_140);
x_333 = lean_array_get_size(x_332);
lean_dec(x_332);
x_334 = lean_nat_dec_eq(x_333, x_29);
lean_dec(x_333);
x_141 = x_334;
goto block_327;
}
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; uint8_t x_493; 
lean_dec(x_140);
x_335 = lean_unsigned_to_nat(5u);
x_336 = l_Lean_Syntax_getArg(x_1, x_335);
lean_inc(x_336);
x_493 = l_Lean_Syntax_isOfKind(x_336, x_328);
if (x_493 == 0)
{
uint8_t x_494; 
x_494 = 0;
x_337 = x_494;
goto block_492;
}
else
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_495 = l_Lean_Syntax_getArgs(x_336);
x_496 = lean_array_get_size(x_495);
lean_dec(x_495);
x_497 = lean_nat_dec_eq(x_496, x_29);
lean_dec(x_496);
x_337 = x_497;
goto block_492;
}
block_492:
{
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_336);
lean_dec(x_138);
lean_dec(x_94);
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
x_344 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_343);
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
x_353 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_352);
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
lean_object* x_357; uint8_t x_358; lean_object* x_485; uint8_t x_486; 
x_357 = l_Lean_Syntax_getArg(x_336, x_51);
lean_dec(x_336);
x_485 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_357);
x_486 = l_Lean_Syntax_isOfKind(x_357, x_485);
if (x_486 == 0)
{
uint8_t x_487; 
x_487 = 0;
x_358 = x_487;
goto block_484;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
x_488 = l_Lean_Syntax_getArgs(x_357);
x_489 = lean_array_get_size(x_488);
lean_dec(x_488);
x_490 = lean_unsigned_to_nat(3u);
x_491 = lean_nat_dec_eq(x_489, x_490);
lean_dec(x_489);
x_358 = x_491;
goto block_484;
}
block_484:
{
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
lean_dec(x_357);
lean_dec(x_138);
lean_dec(x_94);
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
x_365 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_364);
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
x_374 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_373);
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
lean_object* x_378; uint8_t x_379; uint8_t x_479; 
x_378 = l_Lean_Syntax_getArg(x_357, x_51);
lean_inc(x_378);
x_479 = l_Lean_Syntax_isOfKind(x_378, x_328);
if (x_479 == 0)
{
uint8_t x_480; 
x_480 = 0;
x_379 = x_480;
goto block_478;
}
else
{
lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_481 = l_Lean_Syntax_getArgs(x_378);
x_482 = lean_array_get_size(x_481);
lean_dec(x_481);
x_483 = lean_nat_dec_eq(x_482, x_29);
lean_dec(x_482);
x_379 = x_483;
goto block_478;
}
block_478:
{
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_dec(x_378);
lean_dec(x_357);
lean_dec(x_138);
lean_dec(x_94);
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
x_386 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_385);
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
x_395 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_394);
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
lean_object* x_399; uint8_t x_400; lean_object* x_472; uint8_t x_473; 
x_399 = l_Lean_Syntax_getArg(x_378, x_51);
lean_dec(x_378);
x_472 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_399);
x_473 = l_Lean_Syntax_isOfKind(x_399, x_472);
if (x_473 == 0)
{
uint8_t x_474; 
x_474 = 0;
x_400 = x_474;
goto block_471;
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_475 = l_Lean_Syntax_getArgs(x_399);
x_476 = lean_array_get_size(x_475);
lean_dec(x_475);
x_477 = lean_nat_dec_eq(x_476, x_95);
lean_dec(x_476);
x_400 = x_477;
goto block_471;
}
block_471:
{
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
lean_dec(x_399);
lean_dec(x_357);
lean_dec(x_138);
lean_dec(x_94);
x_401 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = l_Lean_Elab_Term_getEnv___rarg(x_402);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_405 = !lean_is_exclusive(x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_ctor_get(x_404, 5);
x_407 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_406);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
lean_ctor_set(x_404, 5, x_409);
x_5 = x_408;
x_6 = x_404;
goto block_8;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_410 = lean_ctor_get(x_404, 0);
x_411 = lean_ctor_get(x_404, 1);
x_412 = lean_ctor_get(x_404, 2);
x_413 = lean_ctor_get(x_404, 3);
x_414 = lean_ctor_get(x_404, 4);
x_415 = lean_ctor_get(x_404, 5);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_404);
x_416 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_419, 0, x_410);
lean_ctor_set(x_419, 1, x_411);
lean_ctor_set(x_419, 2, x_412);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set(x_419, 4, x_414);
lean_ctor_set(x_419, 5, x_418);
x_5 = x_417;
x_6 = x_419;
goto block_8;
}
}
else
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = l_Lean_Syntax_getArg(x_399, x_51);
x_421 = l_Lean_identKind___closed__2;
lean_inc(x_420);
x_422 = l_Lean_Syntax_isOfKind(x_420, x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_420);
lean_dec(x_399);
lean_dec(x_357);
lean_dec(x_138);
lean_dec(x_94);
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
x_429 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_428);
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
x_438 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_437);
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
lean_object* x_442; uint8_t x_443; uint8_t x_466; 
x_442 = l_Lean_Syntax_getArg(x_399, x_29);
lean_dec(x_399);
lean_inc(x_442);
x_466 = l_Lean_Syntax_isOfKind(x_442, x_328);
if (x_466 == 0)
{
uint8_t x_467; 
lean_dec(x_442);
x_467 = 0;
x_443 = x_467;
goto block_465;
}
else
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_468 = l_Lean_Syntax_getArgs(x_442);
lean_dec(x_442);
x_469 = lean_array_get_size(x_468);
lean_dec(x_468);
x_470 = lean_nat_dec_eq(x_469, x_51);
lean_dec(x_469);
x_443 = x_470;
goto block_465;
}
block_465:
{
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
lean_dec(x_420);
lean_dec(x_357);
lean_dec(x_138);
lean_dec(x_94);
x_444 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_446 = l_Lean_Elab_Term_getEnv___rarg(x_445);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = !lean_is_exclusive(x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_447, 5);
x_450 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_449);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_ctor_set(x_447, 5, x_452);
x_5 = x_451;
x_6 = x_447;
goto block_8;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_453 = lean_ctor_get(x_447, 0);
x_454 = lean_ctor_get(x_447, 1);
x_455 = lean_ctor_get(x_447, 2);
x_456 = lean_ctor_get(x_447, 3);
x_457 = lean_ctor_get(x_447, 4);
x_458 = lean_ctor_get(x_447, 5);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_447);
x_459 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_458);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_462, 0, x_453);
lean_ctor_set(x_462, 1, x_454);
lean_ctor_set(x_462, 2, x_455);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set(x_462, 4, x_457);
lean_ctor_set(x_462, 5, x_461);
x_5 = x_460;
x_6 = x_462;
goto block_8;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Lean_Syntax_getArg(x_357, x_95);
lean_dec(x_357);
x_464 = l___private_Lean_Elab_Match_2__expandSimpleMatchWithType(x_1, x_94, x_420, x_138, x_463, x_2, x_3, x_4);
return x_464;
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
block_878:
{
if (x_513 == 0)
{
if (x_512 == 0)
{
uint8_t x_514; 
x_514 = 0;
x_97 = x_514;
goto block_510;
}
else
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_515 = l_Lean_Syntax_getArgs(x_96);
x_516 = lean_array_get_size(x_515);
lean_dec(x_515);
x_517 = lean_nat_dec_eq(x_516, x_29);
lean_dec(x_516);
x_97 = x_517;
goto block_510;
}
}
else
{
lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_704; uint8_t x_705; 
lean_dec(x_96);
x_518 = lean_unsigned_to_nat(4u);
x_519 = l_Lean_Syntax_getArg(x_1, x_518);
lean_inc(x_519);
x_704 = l_Lean_Syntax_isOfKind(x_519, x_511);
if (x_704 == 0)
{
uint8_t x_874; 
x_874 = 0;
x_705 = x_874;
goto block_873;
}
else
{
lean_object* x_875; lean_object* x_876; uint8_t x_877; 
x_875 = l_Lean_Syntax_getArgs(x_519);
x_876 = lean_array_get_size(x_875);
lean_dec(x_875);
x_877 = lean_nat_dec_eq(x_876, x_51);
lean_dec(x_876);
x_705 = x_877;
goto block_873;
}
block_703:
{
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
lean_dec(x_94);
x_521 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_523 = l_Lean_Elab_Term_getEnv___rarg(x_522);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
x_525 = !lean_is_exclusive(x_524);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_524, 5);
x_527 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_526);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_ctor_set(x_524, 5, x_529);
x_5 = x_528;
x_6 = x_524;
goto block_8;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_530 = lean_ctor_get(x_524, 0);
x_531 = lean_ctor_get(x_524, 1);
x_532 = lean_ctor_get(x_524, 2);
x_533 = lean_ctor_get(x_524, 3);
x_534 = lean_ctor_get(x_524, 4);
x_535 = lean_ctor_get(x_524, 5);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_524);
x_536 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_535);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_539, 0, x_530);
lean_ctor_set(x_539, 1, x_531);
lean_ctor_set(x_539, 2, x_532);
lean_ctor_set(x_539, 3, x_533);
lean_ctor_set(x_539, 4, x_534);
lean_ctor_set(x_539, 5, x_538);
x_5 = x_537;
x_6 = x_539;
goto block_8;
}
}
else
{
lean_object* x_540; lean_object* x_541; uint8_t x_542; uint8_t x_698; 
x_540 = lean_unsigned_to_nat(5u);
x_541 = l_Lean_Syntax_getArg(x_1, x_540);
lean_inc(x_541);
x_698 = l_Lean_Syntax_isOfKind(x_541, x_511);
if (x_698 == 0)
{
uint8_t x_699; 
x_699 = 0;
x_542 = x_699;
goto block_697;
}
else
{
lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_700 = l_Lean_Syntax_getArgs(x_541);
x_701 = lean_array_get_size(x_700);
lean_dec(x_700);
x_702 = lean_nat_dec_eq(x_701, x_29);
lean_dec(x_701);
x_542 = x_702;
goto block_697;
}
block_697:
{
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; 
lean_dec(x_541);
lean_dec(x_94);
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
x_549 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_548);
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
x_558 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_557);
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
lean_object* x_562; uint8_t x_563; lean_object* x_690; uint8_t x_691; 
x_562 = l_Lean_Syntax_getArg(x_541, x_51);
lean_dec(x_541);
x_690 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_562);
x_691 = l_Lean_Syntax_isOfKind(x_562, x_690);
if (x_691 == 0)
{
uint8_t x_692; 
x_692 = 0;
x_563 = x_692;
goto block_689;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; 
x_693 = l_Lean_Syntax_getArgs(x_562);
x_694 = lean_array_get_size(x_693);
lean_dec(x_693);
x_695 = lean_unsigned_to_nat(3u);
x_696 = lean_nat_dec_eq(x_694, x_695);
lean_dec(x_694);
x_563 = x_696;
goto block_689;
}
block_689:
{
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; 
lean_dec(x_562);
lean_dec(x_94);
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
x_570 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_569);
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
x_579 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_578);
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
lean_object* x_583; uint8_t x_584; uint8_t x_684; 
x_583 = l_Lean_Syntax_getArg(x_562, x_51);
lean_inc(x_583);
x_684 = l_Lean_Syntax_isOfKind(x_583, x_511);
if (x_684 == 0)
{
uint8_t x_685; 
x_685 = 0;
x_584 = x_685;
goto block_683;
}
else
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_686 = l_Lean_Syntax_getArgs(x_583);
x_687 = lean_array_get_size(x_686);
lean_dec(x_686);
x_688 = lean_nat_dec_eq(x_687, x_29);
lean_dec(x_687);
x_584 = x_688;
goto block_683;
}
block_683:
{
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
lean_dec(x_583);
lean_dec(x_562);
lean_dec(x_94);
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
x_591 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_590);
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
x_600 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_599);
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
lean_object* x_604; uint8_t x_605; lean_object* x_677; uint8_t x_678; 
x_604 = l_Lean_Syntax_getArg(x_583, x_51);
lean_dec(x_583);
x_677 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_604);
x_678 = l_Lean_Syntax_isOfKind(x_604, x_677);
if (x_678 == 0)
{
uint8_t x_679; 
x_679 = 0;
x_605 = x_679;
goto block_676;
}
else
{
lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_680 = l_Lean_Syntax_getArgs(x_604);
x_681 = lean_array_get_size(x_680);
lean_dec(x_680);
x_682 = lean_nat_dec_eq(x_681, x_95);
lean_dec(x_681);
x_605 = x_682;
goto block_676;
}
block_676:
{
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
lean_dec(x_604);
lean_dec(x_562);
lean_dec(x_94);
x_606 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = l_Lean_Elab_Term_getEnv___rarg(x_607);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
lean_dec(x_608);
x_610 = !lean_is_exclusive(x_609);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_609, 5);
x_612 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_611);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
lean_ctor_set(x_609, 5, x_614);
x_5 = x_613;
x_6 = x_609;
goto block_8;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_615 = lean_ctor_get(x_609, 0);
x_616 = lean_ctor_get(x_609, 1);
x_617 = lean_ctor_get(x_609, 2);
x_618 = lean_ctor_get(x_609, 3);
x_619 = lean_ctor_get(x_609, 4);
x_620 = lean_ctor_get(x_609, 5);
lean_inc(x_620);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_609);
x_621 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_620);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_624, 0, x_615);
lean_ctor_set(x_624, 1, x_616);
lean_ctor_set(x_624, 2, x_617);
lean_ctor_set(x_624, 3, x_618);
lean_ctor_set(x_624, 4, x_619);
lean_ctor_set(x_624, 5, x_623);
x_5 = x_622;
x_6 = x_624;
goto block_8;
}
}
else
{
lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_625 = l_Lean_Syntax_getArg(x_604, x_51);
x_626 = l_Lean_identKind___closed__2;
lean_inc(x_625);
x_627 = l_Lean_Syntax_isOfKind(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
lean_dec(x_625);
lean_dec(x_604);
lean_dec(x_562);
lean_dec(x_94);
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
x_634 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_633);
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
x_643 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_642);
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
lean_object* x_647; uint8_t x_648; uint8_t x_671; 
x_647 = l_Lean_Syntax_getArg(x_604, x_29);
lean_dec(x_604);
lean_inc(x_647);
x_671 = l_Lean_Syntax_isOfKind(x_647, x_511);
if (x_671 == 0)
{
uint8_t x_672; 
lean_dec(x_647);
x_672 = 0;
x_648 = x_672;
goto block_670;
}
else
{
lean_object* x_673; lean_object* x_674; uint8_t x_675; 
x_673 = l_Lean_Syntax_getArgs(x_647);
lean_dec(x_647);
x_674 = lean_array_get_size(x_673);
lean_dec(x_673);
x_675 = lean_nat_dec_eq(x_674, x_51);
lean_dec(x_674);
x_648 = x_675;
goto block_670;
}
block_670:
{
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
lean_dec(x_625);
lean_dec(x_562);
lean_dec(x_94);
x_649 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
lean_dec(x_649);
x_651 = l_Lean_Elab_Term_getEnv___rarg(x_650);
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_654 = lean_ctor_get(x_652, 5);
x_655 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_654);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
lean_ctor_set(x_652, 5, x_657);
x_5 = x_656;
x_6 = x_652;
goto block_8;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_658 = lean_ctor_get(x_652, 0);
x_659 = lean_ctor_get(x_652, 1);
x_660 = lean_ctor_get(x_652, 2);
x_661 = lean_ctor_get(x_652, 3);
x_662 = lean_ctor_get(x_652, 4);
x_663 = lean_ctor_get(x_652, 5);
lean_inc(x_663);
lean_inc(x_662);
lean_inc(x_661);
lean_inc(x_660);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_652);
x_664 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_663);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_667, 0, x_658);
lean_ctor_set(x_667, 1, x_659);
lean_ctor_set(x_667, 2, x_660);
lean_ctor_set(x_667, 3, x_661);
lean_ctor_set(x_667, 4, x_662);
lean_ctor_set(x_667, 5, x_666);
x_5 = x_665;
x_6 = x_667;
goto block_8;
}
}
else
{
lean_object* x_668; lean_object* x_669; 
x_668 = l_Lean_Syntax_getArg(x_562, x_95);
lean_dec(x_562);
x_669 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_94, x_625, x_668, x_2, x_3, x_4);
return x_669;
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
block_873:
{
if (x_705 == 0)
{
if (x_704 == 0)
{
uint8_t x_706; 
lean_dec(x_519);
x_706 = 0;
x_520 = x_706;
goto block_703;
}
else
{
lean_object* x_707; lean_object* x_708; uint8_t x_709; 
x_707 = l_Lean_Syntax_getArgs(x_519);
lean_dec(x_519);
x_708 = lean_array_get_size(x_707);
lean_dec(x_707);
x_709 = lean_nat_dec_eq(x_708, x_29);
lean_dec(x_708);
x_520 = x_709;
goto block_703;
}
}
else
{
lean_object* x_710; lean_object* x_711; uint8_t x_712; uint8_t x_868; 
lean_dec(x_519);
x_710 = lean_unsigned_to_nat(5u);
x_711 = l_Lean_Syntax_getArg(x_1, x_710);
lean_inc(x_711);
x_868 = l_Lean_Syntax_isOfKind(x_711, x_511);
if (x_868 == 0)
{
uint8_t x_869; 
x_869 = 0;
x_712 = x_869;
goto block_867;
}
else
{
lean_object* x_870; lean_object* x_871; uint8_t x_872; 
x_870 = l_Lean_Syntax_getArgs(x_711);
x_871 = lean_array_get_size(x_870);
lean_dec(x_870);
x_872 = lean_nat_dec_eq(x_871, x_29);
lean_dec(x_871);
x_712 = x_872;
goto block_867;
}
block_867:
{
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; 
lean_dec(x_711);
lean_dec(x_94);
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
x_719 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_718);
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
x_728 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_727);
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
lean_object* x_732; uint8_t x_733; lean_object* x_860; uint8_t x_861; 
x_732 = l_Lean_Syntax_getArg(x_711, x_51);
lean_dec(x_711);
x_860 = l_Lean_Parser_Term_matchAlt___closed__2;
lean_inc(x_732);
x_861 = l_Lean_Syntax_isOfKind(x_732, x_860);
if (x_861 == 0)
{
uint8_t x_862; 
x_862 = 0;
x_733 = x_862;
goto block_859;
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_863 = l_Lean_Syntax_getArgs(x_732);
x_864 = lean_array_get_size(x_863);
lean_dec(x_863);
x_865 = lean_unsigned_to_nat(3u);
x_866 = lean_nat_dec_eq(x_864, x_865);
lean_dec(x_864);
x_733 = x_866;
goto block_859;
}
block_859:
{
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
lean_dec(x_732);
lean_dec(x_94);
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
x_740 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_739);
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
x_749 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_748);
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
lean_object* x_753; uint8_t x_754; uint8_t x_854; 
x_753 = l_Lean_Syntax_getArg(x_732, x_51);
lean_inc(x_753);
x_854 = l_Lean_Syntax_isOfKind(x_753, x_511);
if (x_854 == 0)
{
uint8_t x_855; 
x_855 = 0;
x_754 = x_855;
goto block_853;
}
else
{
lean_object* x_856; lean_object* x_857; uint8_t x_858; 
x_856 = l_Lean_Syntax_getArgs(x_753);
x_857 = lean_array_get_size(x_856);
lean_dec(x_856);
x_858 = lean_nat_dec_eq(x_857, x_29);
lean_dec(x_857);
x_754 = x_858;
goto block_853;
}
block_853:
{
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; 
lean_dec(x_753);
lean_dec(x_732);
lean_dec(x_94);
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
x_761 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_760);
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
x_770 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_769);
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
lean_object* x_774; uint8_t x_775; lean_object* x_847; uint8_t x_848; 
x_774 = l_Lean_Syntax_getArg(x_753, x_51);
lean_dec(x_753);
x_847 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_774);
x_848 = l_Lean_Syntax_isOfKind(x_774, x_847);
if (x_848 == 0)
{
uint8_t x_849; 
x_849 = 0;
x_775 = x_849;
goto block_846;
}
else
{
lean_object* x_850; lean_object* x_851; uint8_t x_852; 
x_850 = l_Lean_Syntax_getArgs(x_774);
x_851 = lean_array_get_size(x_850);
lean_dec(x_850);
x_852 = lean_nat_dec_eq(x_851, x_95);
lean_dec(x_851);
x_775 = x_852;
goto block_846;
}
block_846:
{
if (x_775 == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
lean_dec(x_774);
lean_dec(x_732);
lean_dec(x_94);
x_776 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
lean_dec(x_776);
x_778 = l_Lean_Elab_Term_getEnv___rarg(x_777);
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
lean_dec(x_778);
x_780 = !lean_is_exclusive(x_779);
if (x_780 == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_781 = lean_ctor_get(x_779, 5);
x_782 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_781);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
lean_ctor_set(x_779, 5, x_784);
x_5 = x_783;
x_6 = x_779;
goto block_8;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_785 = lean_ctor_get(x_779, 0);
x_786 = lean_ctor_get(x_779, 1);
x_787 = lean_ctor_get(x_779, 2);
x_788 = lean_ctor_get(x_779, 3);
x_789 = lean_ctor_get(x_779, 4);
x_790 = lean_ctor_get(x_779, 5);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
lean_inc(x_786);
lean_inc(x_785);
lean_dec(x_779);
x_791 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_790);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_794, 0, x_785);
lean_ctor_set(x_794, 1, x_786);
lean_ctor_set(x_794, 2, x_787);
lean_ctor_set(x_794, 3, x_788);
lean_ctor_set(x_794, 4, x_789);
lean_ctor_set(x_794, 5, x_793);
x_5 = x_792;
x_6 = x_794;
goto block_8;
}
}
else
{
lean_object* x_795; lean_object* x_796; uint8_t x_797; 
x_795 = l_Lean_Syntax_getArg(x_774, x_51);
x_796 = l_Lean_identKind___closed__2;
lean_inc(x_795);
x_797 = l_Lean_Syntax_isOfKind(x_795, x_796);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
lean_dec(x_795);
lean_dec(x_774);
lean_dec(x_732);
lean_dec(x_94);
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
x_804 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_803);
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
x_813 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_812);
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
lean_object* x_817; uint8_t x_818; uint8_t x_841; 
x_817 = l_Lean_Syntax_getArg(x_774, x_29);
lean_dec(x_774);
lean_inc(x_817);
x_841 = l_Lean_Syntax_isOfKind(x_817, x_511);
if (x_841 == 0)
{
uint8_t x_842; 
lean_dec(x_817);
x_842 = 0;
x_818 = x_842;
goto block_840;
}
else
{
lean_object* x_843; lean_object* x_844; uint8_t x_845; 
x_843 = l_Lean_Syntax_getArgs(x_817);
lean_dec(x_817);
x_844 = lean_array_get_size(x_843);
lean_dec(x_843);
x_845 = lean_nat_dec_eq(x_844, x_51);
lean_dec(x_844);
x_818 = x_845;
goto block_840;
}
block_840:
{
if (x_818 == 0)
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
lean_dec(x_795);
lean_dec(x_732);
lean_dec(x_94);
x_819 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
lean_dec(x_819);
x_821 = l_Lean_Elab_Term_getEnv___rarg(x_820);
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec(x_821);
x_823 = !lean_is_exclusive(x_822);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_822, 5);
x_825 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_824);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
lean_ctor_set(x_822, 5, x_827);
x_5 = x_826;
x_6 = x_822;
goto block_8;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_828 = lean_ctor_get(x_822, 0);
x_829 = lean_ctor_get(x_822, 1);
x_830 = lean_ctor_get(x_822, 2);
x_831 = lean_ctor_get(x_822, 3);
x_832 = lean_ctor_get(x_822, 4);
x_833 = lean_ctor_get(x_822, 5);
lean_inc(x_833);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_822);
x_834 = l___private_Lean_Elab_Match_7__expandMatchDiscr_x3f___rarg(x_833);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_834, 1);
lean_inc(x_836);
lean_dec(x_834);
x_837 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_837, 0, x_828);
lean_ctor_set(x_837, 1, x_829);
lean_ctor_set(x_837, 2, x_830);
lean_ctor_set(x_837, 3, x_831);
lean_ctor_set(x_837, 4, x_832);
lean_ctor_set(x_837, 5, x_836);
x_5 = x_835;
x_6 = x_837;
goto block_8;
}
}
else
{
lean_object* x_838; lean_object* x_839; 
x_838 = l_Lean_Syntax_getArg(x_732, x_95);
lean_dec(x_732);
x_839 = l___private_Lean_Elab_Match_1__expandSimpleMatch(x_1, x_94, x_795, x_838, x_2, x_3, x_4);
return x_839;
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
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__1);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__2);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__3);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__4);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__5);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__6);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__7);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__8);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__9);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__10);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__11);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__12);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__13);
l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14 = _init_l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Match_3__expandMatchOptTypeAux___main___closed__14);
l___private_Lean_Elab_Match_6__elabMatchCore___closed__1 = _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabMatchCore___closed__1);
l___private_Lean_Elab_Match_6__elabMatchCore___closed__2 = _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabMatchCore___closed__2);
l___private_Lean_Elab_Match_6__elabMatchCore___closed__3 = _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabMatchCore___closed__3);
l___private_Lean_Elab_Match_6__elabMatchCore___closed__4 = _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabMatchCore___closed__4);
l___private_Lean_Elab_Match_6__elabMatchCore___closed__5 = _init_l___private_Lean_Elab_Match_6__elabMatchCore___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Match_6__elabMatchCore___closed__5);
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
