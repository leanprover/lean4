// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: Init Lean.Parser.Term Lean.Elab.Match Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Induction
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
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_AuxMatchTermState_cases___default;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2;
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_syntheticHole___elambda__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
uint8_t l_Lean_Elab_Term_isAuxDiscrName(lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_stx___x3f___closed__3;
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3;
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14543____closed__10;
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13941____closed__13;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1;
extern lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
extern lean_object* l_Lean_Parser_Tactic_paren___closed__1;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_refine___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntroMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_refine___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_case___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__5;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16029____closed__12;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__3;
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1471____closed__8;
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1;
extern lean_object* l_Lean_Parser_Tactic_case___closed__2;
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14543____closed__13;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6170____closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14543____closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14543____closed__2;
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_6, x_4);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_userName(x_10);
x_12 = l_Lean_Elab_Term_isAuxDiscrName(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3;
x_7 = lean_usize_to_nat(x_6);
x_8 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3;
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_tryClear(x_2, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_1 = x_14;
x_2 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(x_3, x_13, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(x_15, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
x_20 = l_Lean_Elab_Tactic_setGoals(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed), 12, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_13, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_AuxMatchTermState_cases___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rhs");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = x_5;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
x_26 = x_13;
x_27 = l_myMacro____x40_Init_Notation___hyg_14543____closed__10;
x_28 = l_Lean_Syntax_setKind(x_26, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Syntax_getArg(x_28, x_29);
x_31 = l_Lean_Parser_Term_syntheticHole___elambda__1___closed__1;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_myMacro____x40_Init_Notation___hyg_14543____closed__13;
lean_inc(x_30);
x_34 = l_Lean_Syntax_isOfKind(x_30, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_8, x_35);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 5);
lean_inc(x_41);
lean_inc(x_8);
lean_inc(x_38);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_8);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_41);
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_6, x_42, x_36);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_stx___x3f___closed__3;
lean_inc(x_46);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_empty___closed__1;
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4;
x_53 = l_Lean_addMacroScope(x_38, x_52, x_8);
x_54 = lean_box(0);
x_55 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3;
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_54);
x_57 = lean_array_push(x_51, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_31);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Syntax_getArg(x_58, x_35);
x_60 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_47, x_42, x_45);
lean_dec(x_42);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
x_66 = l_Lean_Parser_Tactic_case___closed__1;
lean_inc(x_64);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_50, x_67);
x_69 = lean_array_push(x_68, x_59);
x_70 = l_myMacro____x40_Init_Notation___hyg_13941____closed__13;
lean_inc(x_64);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_69, x_71);
x_73 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_inc(x_64);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_50, x_74);
x_76 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_50, x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_16029____closed__12;
lean_inc(x_64);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_64);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_array_push(x_50, x_80);
x_82 = l_Lean_nullKind___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_78, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_50, x_85);
x_87 = l_prec_x28___x29___closed__3;
lean_inc(x_64);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_push(x_50, x_88);
x_90 = lean_array_push(x_89, x_30);
x_91 = l_prec_x28___x29___closed__7;
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_64);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_90, x_92);
x_94 = l_Lean_Parser_Tactic_paren___closed__1;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_array_push(x_50, x_95);
x_97 = l_myMacro____x40_Init_Notation___hyg_1471____closed__8;
x_98 = lean_array_push(x_96, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_82);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_86, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_push(x_50, x_101);
x_103 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__5;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_array_push(x_50, x_104);
x_106 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__3;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_72, x_107);
x_109 = l_Lean_Parser_Tactic_case___closed__2;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = !lean_is_exclusive(x_65);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_65, 1);
x_113 = lean_array_push(x_112, x_110);
lean_ctor_set(x_65, 1, x_113);
x_114 = l_Lean_Syntax_setArg(x_28, x_29, x_58);
lean_ctor_set(x_61, 0, x_114);
x_16 = x_61;
x_17 = x_62;
goto block_25;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_65, 0);
x_116 = lean_ctor_get(x_65, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_65);
x_117 = lean_array_push(x_116, x_110);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Syntax_setArg(x_28, x_29, x_58);
lean_ctor_set(x_61, 1, x_118);
lean_ctor_set(x_61, 0, x_119);
x_16 = x_61;
x_17 = x_62;
goto block_25;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_120 = lean_ctor_get(x_61, 0);
x_121 = lean_ctor_get(x_61, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_61);
x_122 = l_Lean_Parser_Tactic_case___closed__1;
lean_inc(x_120);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_50, x_123);
x_125 = lean_array_push(x_124, x_59);
x_126 = l_myMacro____x40_Init_Notation___hyg_13941____closed__13;
lean_inc(x_120);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_push(x_125, x_127);
x_129 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_inc(x_120);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_push(x_50, x_130);
x_132 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_array_push(x_50, x_133);
x_135 = l_myMacro____x40_Init_Notation___hyg_16029____closed__12;
lean_inc(x_120);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_120);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_array_push(x_50, x_136);
x_138 = l_Lean_nullKind___closed__2;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_array_push(x_134, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_array_push(x_50, x_141);
x_143 = l_prec_x28___x29___closed__3;
lean_inc(x_120);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_120);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_array_push(x_50, x_144);
x_146 = lean_array_push(x_145, x_30);
x_147 = l_prec_x28___x29___closed__7;
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_120);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_push(x_146, x_148);
x_150 = l_Lean_Parser_Tactic_paren___closed__1;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_array_push(x_50, x_151);
x_153 = l_myMacro____x40_Init_Notation___hyg_1471____closed__8;
x_154 = lean_array_push(x_152, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_138);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_push(x_142, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_138);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_50, x_157);
x_159 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__5;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_array_push(x_50, x_160);
x_162 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17269____closed__3;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_128, x_163);
x_165 = l_Lean_Parser_Tactic_case___closed__2;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_ctor_get(x_121, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_121, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_169 = x_121;
} else {
 lean_dec_ref(x_121);
 x_169 = lean_box(0);
}
x_170 = lean_array_push(x_168, x_166);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_Syntax_setArg(x_28, x_29, x_58);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_16 = x_173;
x_17 = x_62;
goto block_25;
}
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_174 = lean_array_get_size(x_2);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_dec_lt(x_175, x_174);
lean_dec(x_174);
lean_inc(x_6);
x_177 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_6, x_7, x_8);
if (x_176 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_dec(x_6);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_1);
x_180 = l_Lean_mkIdentFrom(x_30, x_1);
lean_dec(x_30);
x_181 = !lean_is_exclusive(x_178);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_182 = lean_ctor_get(x_178, 0);
x_183 = lean_ctor_get(x_178, 1);
x_184 = l_stx___x3f___closed__3;
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Array_empty___closed__1;
x_187 = lean_array_push(x_186, x_185);
x_188 = lean_array_push(x_187, x_180);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_31);
lean_ctor_set(x_189, 1, x_188);
x_190 = !lean_is_exclusive(x_183);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_183, 0);
x_192 = lean_nat_add(x_191, x_175);
lean_dec(x_191);
lean_ctor_set(x_183, 0, x_192);
x_193 = l_Lean_Syntax_setArg(x_28, x_29, x_189);
lean_ctor_set(x_178, 0, x_193);
x_16 = x_178;
x_17 = x_179;
goto block_25;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_183, 0);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_183);
x_196 = lean_nat_add(x_194, x_175);
lean_dec(x_194);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l_Lean_Syntax_setArg(x_28, x_29, x_189);
lean_ctor_set(x_178, 1, x_197);
lean_ctor_set(x_178, 0, x_198);
x_16 = x_178;
x_17 = x_179;
goto block_25;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_199 = lean_ctor_get(x_178, 0);
x_200 = lean_ctor_get(x_178, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_178);
x_201 = l_stx___x3f___closed__3;
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Array_empty___closed__1;
x_204 = lean_array_push(x_203, x_202);
x_205 = lean_array_push(x_204, x_180);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_31);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
x_210 = lean_nat_add(x_207, x_175);
lean_dec(x_207);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
x_212 = l_Lean_Syntax_setArg(x_28, x_29, x_206);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_16 = x_213;
x_17 = x_179;
goto block_25;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_214 = lean_ctor_get(x_177, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_177, 1);
lean_inc(x_215);
lean_dec(x_177);
x_216 = lean_ctor_get(x_6, 0);
lean_inc(x_216);
lean_dec(x_6);
x_217 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_6170____closed__1;
x_218 = l_Lean_Name_appendIndexAfter(x_217, x_216);
x_219 = l_Lean_Name_append(x_1, x_218);
x_220 = l_Lean_mkIdentFrom(x_30, x_219);
lean_dec(x_30);
x_221 = !lean_is_exclusive(x_214);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_222 = lean_ctor_get(x_214, 0);
x_223 = lean_ctor_get(x_214, 1);
x_224 = l_stx___x3f___closed__3;
x_225 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Array_empty___closed__1;
x_227 = lean_array_push(x_226, x_225);
x_228 = lean_array_push(x_227, x_220);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_31);
lean_ctor_set(x_229, 1, x_228);
x_230 = !lean_is_exclusive(x_223);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_223, 0);
x_232 = lean_nat_add(x_231, x_175);
lean_dec(x_231);
lean_ctor_set(x_223, 0, x_232);
x_233 = l_Lean_Syntax_setArg(x_28, x_29, x_229);
lean_ctor_set(x_214, 0, x_233);
x_16 = x_214;
x_17 = x_215;
goto block_25;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_223, 0);
x_235 = lean_ctor_get(x_223, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_223);
x_236 = lean_nat_add(x_234, x_175);
lean_dec(x_234);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_Syntax_setArg(x_28, x_29, x_229);
lean_ctor_set(x_214, 1, x_237);
lean_ctor_set(x_214, 0, x_238);
x_16 = x_214;
x_17 = x_215;
goto block_25;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_239 = lean_ctor_get(x_214, 0);
x_240 = lean_ctor_get(x_214, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_214);
x_241 = l_stx___x3f___closed__3;
x_242 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Array_empty___closed__1;
x_244 = lean_array_push(x_243, x_242);
x_245 = lean_array_push(x_244, x_220);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_31);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_ctor_get(x_240, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_240, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_249 = x_240;
} else {
 lean_dec_ref(x_240);
 x_249 = lean_box(0);
}
x_250 = lean_nat_add(x_247, x_175);
lean_dec(x_247);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
x_252 = l_Lean_Syntax_setArg(x_28, x_29, x_246);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
x_16 = x_253;
x_17 = x_215;
goto block_25;
}
}
}
}
else
{
lean_object* x_254; 
lean_dec(x_30);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_28);
lean_ctor_set(x_254, 1, x_6);
x_16 = x_254;
x_17 = x_8;
goto block_25;
}
block_25:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = x_4 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_15, x_4, x_22);
x_4 = x_21;
x_5 = x_23;
x_6 = x_19;
x_8 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
lean_inc(x_10);
x_13 = x_10;
x_14 = lean_box_usize(x_12);
x_15 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1;
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed), 8, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_10);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_13);
x_17 = x_16;
x_18 = lean_apply_3(x_17, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_myMacro____x40_Init_Notation___hyg_14543____closed__2;
x_24 = l_Lean_Syntax_setKind(x_2, x_23);
x_25 = l_Lean_nullKind;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_myMacro____x40_Init_Notation___hyg_14543____closed__8;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Syntax_setArg(x_24, x_6, x_30);
lean_ctor_set(x_20, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = l_myMacro____x40_Init_Notation___hyg_14543____closed__2;
x_35 = l_Lean_Syntax_setKind(x_2, x_34);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = l_Lean_mkOptionalNode___closed__2;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_myMacro____x40_Init_Notation___hyg_14543____closed__8;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Syntax_setArg(x_35, x_6, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_18, 0, x_43);
return x_18;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = l_myMacro____x40_Init_Notation___hyg_14543____closed__2;
x_50 = l_Lean_Syntax_setKind(x_2, x_49);
x_51 = l_Lean_nullKind;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = l_Lean_mkOptionalNode___closed__2;
x_54 = lean_array_push(x_53, x_52);
x_55 = l_myMacro____x40_Init_Notation___hyg_14543____closed__8;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Syntax_setArg(x_50, x_6, x_56);
if (lean_is_scalar(x_48)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_48;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1() {
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
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1;
x_6 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(x_1, x_2, x_5, x_3, x_4);
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
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_40 = lean_st_ref_get(x_9, x_13);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_8, 3);
lean_inc(x_44);
x_45 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 2);
lean_inc(x_49);
x_50 = lean_st_ref_get(x_9, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_43);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_54, 0, x_43);
x_55 = x_54;
x_56 = lean_environment_main_module(x_43);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_46);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set(x_57, 4, x_49);
lean_ctor_set(x_57, 5, x_44);
lean_inc(x_1);
x_58 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(x_12, x_1, x_57, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_take(x_9, x_52);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_dec(x_65);
lean_ctor_set(x_62, 1, x_60);
x_66 = lean_st_ref_set(x_9, x_62, x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_14 = x_59;
x_15 = x_67;
goto block_39;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 2);
x_70 = lean_ctor_get(x_62, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_60);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_st_ref_set(x_9, x_71, x_63);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_14 = x_59;
x_15 = x_73;
goto block_39;
}
}
else
{
lean_object* x_74; 
lean_dec(x_1);
x_74 = lean_ctor_get(x_58, 0);
lean_inc(x_74);
lean_dec(x_58);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(x_75, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_75);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(x_52);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(x_8, x_9, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_Tactic_refine___closed__1;
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_empty___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_array_push(x_28, x_16);
x_30 = l_Lean_Parser_Tactic_refine___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_mkOptionalNode___closed__2;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Array_append___rarg(x_33, x_17);
lean_dec(x_17);
x_35 = l_Lean_nullKind;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_36);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntroMatch___lambda__1), 11, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_38;
}
}
else
{
uint8_t x_89; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_11);
if (x_89 == 0)
{
return x_11;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_11, 0);
x_91 = lean_ctor_get(x_11, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_11);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1() {
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
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
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
res = initialize_Lean_Parser_Term(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default = _init_l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default();
lean_mark_persistent(l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default);
l_Lean_Elab_Tactic_AuxMatchTermState_cases___default = _init_l_Lean_Elab_Tactic_AuxMatchTermState_cases___default();
lean_mark_persistent(l_Lean_Elab_Tactic_AuxMatchTermState_cases___default);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4);
l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1);
l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1 = _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1);
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
