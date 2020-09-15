// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: Init Lean.Elab.Match Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Induction
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
lean_object* l_Lean_Syntax_updateKind(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__3;
lean_object* l_Lean_Elab_Tactic_evalMatch___closed__2;
lean_object* l_Lean_Elab_Tactic_mkTacticSeq___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2;
extern lean_object* l_Lean_Elab_Tactic_evalCase___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticSeq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___rarg(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalCase___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Match_38__elabMatchAux___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalRefine___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Error_toString___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__10;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalRefine___closed__1;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__4;
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__17;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
lean_object* l_Lean_Elab_Tactic_evalMatch___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mod(x_3, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_12);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_inc(x_2);
lean_inc(x_6);
x_21 = lean_apply_4(x_2, x_12, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_28 = lean_array_push(x_4, x_24);
x_3 = x_27;
x_4 = x_28;
x_5 = x_25;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2(x_1, x_2, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Tactic_evalCase___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__18;
x_7 = l_Lean_Syntax_updateKind(x_2, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
x_10 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_mkHole___closed__2;
lean_inc(x_9);
x_13 = l_Lean_Syntax_isOfKind(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__4;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_5);
x_19 = lean_box(0);
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__3;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
x_23 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Syntax_getArg(x_25, x_14);
x_27 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__17;
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_array_push(x_30, x_9);
x_32 = l_Lean_Elab_Tactic_evalCase___closed__5;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_array_push(x_35, x_33);
lean_ctor_set(x_3, 1, x_36);
x_37 = l_Lean_Syntax_setArg(x_7, x_8, x_25);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_15);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = lean_array_push(x_41, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Syntax_setArg(x_7, x_8, x_25);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_15);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__2;
lean_inc(x_48);
x_50 = l_Lean_Name_appendIndexAfter(x_49, x_48);
x_51 = l_Lean_Name_append___main(x_1, x_50);
x_52 = l_Lean_mkIdentFrom(x_9, x_51);
lean_dec(x_9);
x_53 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_48, x_56);
lean_dec(x_48);
lean_ctor_set(x_3, 0, x_57);
x_58 = l_Lean_Syntax_setArg(x_7, x_8, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_3, 0);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_3);
x_63 = l___private_Lean_Elab_Match_38__elabMatchAux___closed__2;
lean_inc(x_61);
x_64 = l_Lean_Name_appendIndexAfter(x_63, x_61);
x_65 = l_Lean_Name_append___main(x_1, x_64);
x_66 = l_Lean_mkIdentFrom(x_9, x_65);
lean_dec(x_9);
x_67 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_10);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_61, x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_62);
x_73 = l_Lean_Syntax_setArg(x_7, x_8, x_69);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
lean_dec(x_4);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_7);
lean_ctor_set(x_76, 1, x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
return x_77;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___boxed), 5, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1(x_10, x_11, x_3, x_4, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_18 = l_Lean_Syntax_updateKind(x_2, x_17);
x_19 = l_Lean_nullKind;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_Lean_Syntax_setArg(x_7, x_8, x_20);
x_22 = l_Lean_Syntax_setArg(x_18, x_6, x_21);
lean_ctor_set(x_14, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_26 = l_Lean_Syntax_updateKind(x_2, x_25);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = l_Lean_Syntax_setArg(x_7, x_8, x_28);
x_30 = l_Lean_Syntax_setArg(x_26, x_6, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
x_37 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_38 = l_Lean_Syntax_updateKind(x_2, x_37);
x_39 = l_Lean_nullKind;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = l_Lean_Syntax_setArg(x_7, x_8, x_40);
x_42 = l_Lean_Syntax_setArg(x_38, x_6, x_41);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_33);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
return x_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapSepElemsM___at___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1;
x_6 = l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux(x_1, x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_ctor_set(x_7, 1, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_19 = x_7;
} else {
 lean_dec_ref(x_7);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticSeq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_Error_toString___closed__2;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkSepStx(x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticSeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_mkTacticSeq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___rarg), 1, 0);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Tactic_evalRefine___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Tactic_evalMatch___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_49; 
lean_inc(x_4);
x_49 = l_Lean_Elab_Tactic_getMainTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_get(x_9, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_5, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 3);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_8, 2);
lean_inc(x_64);
x_65 = lean_environment_main_module(x_58);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_64);
lean_inc(x_1);
x_67 = l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm(x_50, x_1, x_66, x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_take(x_5, x_61);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 3);
lean_dec(x_74);
lean_ctor_set(x_71, 3, x_69);
x_75 = lean_st_ref_set(x_5, x_71, x_72);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_11 = x_68;
x_12 = x_76;
goto block_48;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
x_79 = lean_ctor_get(x_71, 2);
x_80 = lean_ctor_get(x_71, 4);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_69);
lean_ctor_set(x_81, 4, x_80);
x_82 = lean_st_ref_set(x_5, x_81, x_72);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_11 = x_68;
x_12 = x_83;
goto block_48;
}
}
else
{
lean_object* x_84; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_67, 0);
lean_inc(x_84);
lean_dec(x_67);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_85, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_85);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___rarg(x_61);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_49);
if (x_99 == 0)
{
return x_49;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_49, 0);
x_101 = lean_ctor_get(x_49, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_49);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
block_48:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Elab_Tactic_getCurrMacroScope___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_getMainModule___rarg(x_9, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_evalMatch___closed__2;
x_20 = lean_array_push(x_19, x_13);
x_21 = l_Lean_Elab_Tactic_evalRefine___closed__3;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_14, x_14, x_25, x_24);
lean_dec(x_14);
x_27 = l_Lean_Elab_Tactic_mkTacticSeq(x_1, x_26);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_4, 6);
lean_inc(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_4, 6, x_31);
x_32 = l_Lean_Elab_Tactic_evalTactic___main(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
x_35 = lean_ctor_get(x_4, 2);
x_36 = lean_ctor_get(x_4, 3);
x_37 = lean_ctor_get(x_4, 4);
x_38 = lean_ctor_get(x_4, 5);
x_39 = lean_ctor_get(x_4, 6);
x_40 = lean_ctor_get(x_4, 7);
x_41 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_42 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
lean_inc(x_27);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
x_46 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_35);
lean_ctor_set(x_46, 3, x_36);
lean_ctor_set(x_46, 4, x_37);
lean_ctor_set(x_46, 5, x_38);
lean_ctor_set(x_46, 6, x_45);
lean_ctor_set(x_46, 7, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*8, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 2, x_43);
x_47 = l_Lean_Elab_Tactic_evalTactic___main(x_27, x_2, x_3, x_46, x_5, x_6, x_7, x_8, x_9, x_18);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Match(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4 = _init_l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_1__mkAuxiliaryMatchTermAux___lambda__1___closed__4);
l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1 = _init_l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_2__mkAuxiliaryMatchTerm___closed__1);
l_Lean_Elab_Tactic_evalMatch___closed__1 = _init_l_Lean_Elab_Tactic_evalMatch___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalMatch___closed__1);
l_Lean_Elab_Tactic_evalMatch___closed__2 = _init_l_Lean_Elab_Tactic_evalMatch___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalMatch___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
