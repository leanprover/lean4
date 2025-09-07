// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
// Imports: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide Lean.Elab.Tactic.BVDecide.Frontend.BVCheck Lean.Elab.Tactic.BVDecide.LRAT.Trim Lean.Meta.Tactic.TryThis Std.Tactic.BVDecide.Syntax
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0;
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1;
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15;
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16;
static lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17;
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("while expanding", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_dec(x_9);
lean_inc_ref(x_1);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_2);
x_10 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_8);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
x_18 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2;
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = l_Lean_MessageData_ofSyntax(x_16);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_21;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc_ref(x_1);
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(7, 2, 0);
} else {
 x_27 = x_26;
 lean_ctor_set_tag(x_27, 7);
}
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_1);
x_28 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofSyntax(x_25);
x_31 = l_Lean_indentD(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_2 = x_32;
x_3 = x_24;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_pp_macroStack;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("with resulting expansion", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0;
x_7 = l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2(x_14, x_19, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2(x_23, x_29, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(x_1, x_2, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
x_15 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(x_12, x_14, x_6, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_Lean_Elab_getBetterRef(x_9, x_14);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec_ref(x_2);
lean_inc(x_25);
x_26 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(x_23, x_25, x_6, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Elab_getBetterRef(x_9, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_29;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = 0;
x_5 = l_Lean_Syntax_getPos_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg(x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not find file name", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not find declaration name", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lrat", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_10 = l_System_FilePath_fileName(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1;
x_12 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_1, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
x_18 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg(x_5, x_19);
lean_dec_ref(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_FileMap_toPosition(x_9, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
x_28 = lean_string_append(x_13, x_27);
x_29 = 1;
x_30 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_20, x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec_ref(x_30);
x_32 = lean_string_append(x_31, x_27);
x_33 = l_Nat_reprFast(x_25);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = lean_string_append(x_34, x_27);
x_36 = l_Nat_reprFast(x_26);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = l_Lean_FileMap_toPosition(x_9, x_40);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
x_46 = lean_string_append(x_13, x_45);
x_47 = 1;
x_48 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_20, x_47);
x_49 = lean_string_append(x_46, x_48);
lean_dec_ref(x_48);
x_50 = lean_string_append(x_49, x_45);
x_51 = l_Nat_reprFast(x_43);
x_52 = lean_string_append(x_50, x_51);
lean_dec_ref(x_51);
x_53 = lean_string_append(x_52, x_45);
x_54 = l_Nat_reprFast(x_44);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getRefPos___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_mk_io_user_error(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvTrace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvCheck", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bv_check", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this:", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvNormalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bv_normalize", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg(x_10);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_15);
x_19 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_15, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 1);
x_27 = 0;
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_27);
lean_inc_ref(x_4);
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_23, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc(x_29);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed), 11, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_29);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_35 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(x_32, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
lean_dec(x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
x_62 = lean_ctor_get(x_8, 5);
x_63 = l_Lean_SourceInfo_fromRef(x_62, x_27);
x_64 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
x_65 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14;
x_66 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15;
lean_inc(x_63);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17;
x_69 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18;
lean_inc(x_63);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_63);
x_71 = l_Lean_Syntax_node1(x_63, x_16, x_70);
x_72 = l_Lean_Syntax_node2(x_63, x_65, x_67, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_36);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_74);
lean_inc(x_62);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_62);
x_77 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12;
x_78 = 4;
x_79 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_39, x_75, x_76, x_77, x_36, x_78, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_36);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_36, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_29, 5);
lean_inc_ref(x_82);
lean_dec(x_29);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
lean_dec_ref(x_82);
if (x_83 == 0)
{
lean_free_object(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_37;
goto block_61;
}
else
{
lean_object* x_84; 
x_84 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_5);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_System_FilePath_join(x_85, x_23);
x_88 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_87, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_89);
lean_dec(x_89);
x_92 = l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(x_91, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_87, x_93, x_26, x_94);
lean_dec(x_93);
lean_dec_ref(x_87);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_free_object(x_36);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_96;
goto block_61;
}
else
{
uint8_t x_97; 
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_8, 5);
lean_inc(x_99);
lean_dec_ref(x_8);
x_100 = lean_io_error_to_string(x_98);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_100);
x_101 = l_Lean_MessageData_ofFormat(x_36);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_95, 0, x_102);
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_95, 0);
x_104 = lean_ctor_get(x_95, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_95);
x_105 = lean_ctor_get(x_8, 5);
lean_inc(x_105);
lean_dec_ref(x_8);
x_106 = lean_io_error_to_string(x_103);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_106);
x_107 = l_Lean_MessageData_ofFormat(x_36);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec_ref(x_87);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_110 = !lean_is_exclusive(x_92);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_8, 5);
lean_inc(x_112);
lean_dec_ref(x_8);
x_113 = lean_io_error_to_string(x_111);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_113);
x_114 = l_Lean_MessageData_ofFormat(x_36);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_92, 0, x_115);
return x_92;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_92, 0);
x_117 = lean_ctor_get(x_92, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_92);
x_118 = lean_ctor_get(x_8, 5);
lean_inc(x_118);
lean_dec_ref(x_8);
x_119 = lean_io_error_to_string(x_116);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_119);
x_120 = l_Lean_MessageData_ofFormat(x_36);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_87);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_123 = !lean_is_exclusive(x_88);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_88, 0);
x_125 = lean_ctor_get(x_8, 5);
lean_inc(x_125);
lean_dec_ref(x_8);
x_126 = lean_io_error_to_string(x_124);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_126);
x_127 = l_Lean_MessageData_ofFormat(x_36);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_88, 0, x_128);
return x_88;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_88, 0);
x_130 = lean_ctor_get(x_88, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_88);
x_131 = lean_ctor_get(x_8, 5);
lean_inc(x_131);
lean_dec_ref(x_8);
x_132 = lean_io_error_to_string(x_129);
lean_ctor_set_tag(x_36, 3);
lean_ctor_set(x_36, 0, x_132);
x_133 = l_Lean_MessageData_ofFormat(x_36);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_free_object(x_36);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_136 = !lean_is_exclusive(x_84);
if (x_136 == 0)
{
return x_84;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_84, 0);
x_138 = lean_ctor_get(x_84, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_84);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; uint8_t x_141; 
lean_dec(x_36);
x_140 = lean_ctor_get(x_29, 5);
lean_inc_ref(x_140);
lean_dec(x_29);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*2);
lean_dec_ref(x_140);
if (x_141 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_37;
goto block_61;
}
else
{
lean_object* x_142; 
x_142 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = l_System_FilePath_join(x_143, x_23);
x_146 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_145, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_147);
lean_dec(x_147);
x_150 = l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(x_149, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
x_153 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_145, x_151, x_26, x_152);
lean_dec(x_151);
lean_dec_ref(x_145);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec_ref(x_153);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
x_43 = x_9;
x_44 = x_154;
goto block_61;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_157 = x_153;
} else {
 lean_dec_ref(x_153);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_8, 5);
lean_inc(x_158);
lean_dec_ref(x_8);
x_159 = lean_io_error_to_string(x_155);
x_160 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = l_Lean_MessageData_ofFormat(x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
if (lean_is_scalar(x_157)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_157;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec_ref(x_145);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_8, 5);
lean_inc(x_167);
lean_dec_ref(x_8);
x_168 = lean_io_error_to_string(x_164);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lean_MessageData_ofFormat(x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_166)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_166;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_165);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_145);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_173 = lean_ctor_get(x_146, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_146, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_175 = x_146;
} else {
 lean_dec_ref(x_146);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_8, 5);
lean_inc(x_176);
lean_dec_ref(x_8);
x_177 = lean_io_error_to_string(x_173);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_MessageData_ofFormat(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_175)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_175;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_174);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_182 = lean_ctor_get(x_142, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_142, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_184 = x_142;
} else {
 lean_dec_ref(x_142);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
block_61:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_42, 5);
x_46 = l_Lean_SourceInfo_fromRef(x_45, x_27);
x_47 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
x_49 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
lean_inc(x_46);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(2);
x_52 = l_Lean_Syntax_mkStrLit(x_23, x_51);
lean_dec(x_23);
x_53 = l_Lean_Syntax_node3(x_46, x_48, x_50, x_15, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_55);
lean_inc(x_45);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_45);
x_58 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12;
x_59 = 4;
x_60 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_39, x_56, x_57, x_58, x_55, x_59, x_40, x_41, x_42, x_43, x_44);
lean_dec(x_41);
lean_dec_ref(x_40);
return x_60;
}
}
else
{
uint8_t x_186; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_35);
if (x_186 == 0)
{
return x_35;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_35, 0);
x_188 = lean_ctor_get(x_35, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_35);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_31);
if (x_190 == 0)
{
return x_31;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_31, 0);
x_192 = lean_ctor_get(x_31, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_31);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_28);
if (x_194 == 0)
{
return x_28;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_28, 0);
x_196 = lean_ctor_get(x_28, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_28);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_20, 0);
x_199 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 1);
x_200 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 2);
x_201 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 3);
x_202 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 4);
x_203 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 5);
x_204 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 6);
x_205 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 7);
x_206 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 8);
x_207 = lean_ctor_get(x_20, 1);
x_208 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 9);
lean_inc(x_207);
lean_inc(x_198);
lean_dec(x_20);
x_209 = 0;
x_210 = lean_alloc_ctor(0, 2, 10);
lean_ctor_set(x_210, 0, x_198);
lean_ctor_set(x_210, 1, x_207);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 1, x_199);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 2, x_200);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 3, x_201);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 4, x_202);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 5, x_203);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 6, x_204);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 7, x_205);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 8, x_206);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 9, x_208);
lean_inc_ref(x_4);
x_211 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_23, x_210, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec_ref(x_211);
x_214 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
lean_inc(x_212);
lean_inc(x_215);
x_217 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed), 11, 2);
lean_closure_set(x_217, 0, x_215);
lean_closure_set(x_217, 1, x_212);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_218 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__1___redArg(x_215, x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_unsigned_to_nat(0u);
x_222 = l_Lean_Syntax_getArg(x_1, x_221);
lean_dec(x_1);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; 
lean_dec(x_212);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
x_245 = lean_ctor_get(x_8, 5);
x_246 = l_Lean_SourceInfo_fromRef(x_245, x_209);
x_247 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
x_248 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14;
x_249 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15;
lean_inc(x_246);
x_250 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17;
x_252 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18;
lean_inc(x_246);
x_253 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_251);
lean_ctor_set(x_253, 2, x_252);
lean_inc(x_246);
x_254 = l_Lean_Syntax_node1(x_246, x_16, x_253);
x_255 = l_Lean_Syntax_node2(x_246, x_248, x_250, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_247);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_219);
lean_ctor_set(x_258, 2, x_219);
lean_ctor_set(x_258, 3, x_257);
lean_ctor_set(x_258, 4, x_257);
lean_ctor_set(x_258, 5, x_257);
lean_inc(x_245);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_245);
x_260 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12;
x_261 = 4;
x_262 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_222, x_258, x_259, x_260, x_219, x_261, x_6, x_7, x_8, x_9, x_220);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_263 = x_219;
} else {
 lean_dec_ref(x_219);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_212, 5);
lean_inc_ref(x_264);
lean_dec(x_212);
x_265 = lean_ctor_get_uint8(x_264, sizeof(void*)*2);
lean_dec_ref(x_264);
if (x_265 == 0)
{
lean_dec(x_263);
lean_dec(x_5);
lean_dec_ref(x_4);
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = x_220;
goto block_244;
}
else
{
lean_object* x_266; 
x_266 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_220);
lean_dec(x_5);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec_ref(x_266);
x_269 = l_System_FilePath_join(x_267, x_23);
x_270 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_269, x_268);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim(x_271);
lean_dec(x_271);
x_274 = l_IO_ofExcept___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__2___redArg(x_273, x_272);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec_ref(x_274);
x_277 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_269, x_275, x_199, x_276);
lean_dec(x_275);
lean_dec_ref(x_269);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
lean_dec(x_263);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec_ref(x_277);
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = x_278;
goto block_244;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_222);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_281 = x_277;
} else {
 lean_dec_ref(x_277);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_8, 5);
lean_inc(x_282);
lean_dec_ref(x_8);
x_283 = lean_io_error_to_string(x_279);
if (lean_is_scalar(x_263)) {
 x_284 = lean_alloc_ctor(3, 1, 0);
} else {
 x_284 = x_263;
 lean_ctor_set_tag(x_284, 3);
}
lean_ctor_set(x_284, 0, x_283);
x_285 = l_Lean_MessageData_ofFormat(x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_285);
if (lean_is_scalar(x_281)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_281;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_280);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec_ref(x_269);
lean_dec(x_222);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_288 = lean_ctor_get(x_274, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_274, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_290 = x_274;
} else {
 lean_dec_ref(x_274);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_8, 5);
lean_inc(x_291);
lean_dec_ref(x_8);
x_292 = lean_io_error_to_string(x_288);
if (lean_is_scalar(x_263)) {
 x_293 = lean_alloc_ctor(3, 1, 0);
} else {
 x_293 = x_263;
 lean_ctor_set_tag(x_293, 3);
}
lean_ctor_set(x_293, 0, x_292);
x_294 = l_Lean_MessageData_ofFormat(x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
if (lean_is_scalar(x_290)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_290;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_289);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec_ref(x_269);
lean_dec(x_222);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
x_297 = lean_ctor_get(x_270, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_270, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_299 = x_270;
} else {
 lean_dec_ref(x_270);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_8, 5);
lean_inc(x_300);
lean_dec_ref(x_8);
x_301 = lean_io_error_to_string(x_297);
if (lean_is_scalar(x_263)) {
 x_302 = lean_alloc_ctor(3, 1, 0);
} else {
 x_302 = x_263;
 lean_ctor_set_tag(x_302, 3);
}
lean_ctor_set(x_302, 0, x_301);
x_303 = l_Lean_MessageData_ofFormat(x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
if (lean_is_scalar(x_299)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_299;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_298);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_263);
lean_dec(x_222);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_306 = lean_ctor_get(x_266, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_266, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_308 = x_266;
} else {
 lean_dec_ref(x_266);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
block_244:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_228 = lean_ctor_get(x_225, 5);
x_229 = l_Lean_SourceInfo_fromRef(x_228, x_209);
x_230 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
x_231 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
x_232 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
lean_inc(x_229);
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_box(2);
x_235 = l_Lean_Syntax_mkStrLit(x_23, x_234);
lean_dec(x_23);
x_236 = l_Lean_Syntax_node3(x_229, x_231, x_233, x_15, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_230);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_238);
lean_ctor_set(x_239, 4, x_238);
lean_ctor_set(x_239, 5, x_238);
lean_inc(x_228);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_228);
x_241 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12;
x_242 = 4;
x_243 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_222, x_239, x_240, x_241, x_238, x_242, x_223, x_224, x_225, x_226, x_227);
lean_dec(x_224);
lean_dec_ref(x_223);
return x_243;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_212);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_310 = lean_ctor_get(x_218, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_218, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_312 = x_218;
} else {
 lean_dec_ref(x_218);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_212);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_314 = lean_ctor_get(x_214, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_214, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_316 = x_214;
} else {
 lean_dec_ref(x_214);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_318 = lean_ctor_get(x_211, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_211, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_320 = x_211;
} else {
 lean_dec_ref(x_211);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_322 = !lean_is_exclusive(x_22);
if (x_322 == 0)
{
return x_22;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_22, 0);
x_324 = lean_ctor_get(x_22, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_22);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_19);
if (x_326 == 0)
{
return x_19;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_19, 0);
x_328 = lean_ctor_get(x_19, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_19);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVDecide", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Frontend", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVTrace", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalBvTrace", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5;
x_2 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4;
x_3 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3;
x_4 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2;
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_6 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1;
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0;
x_8 = l_Lean_Name_mkStr7(x_7, x_6, x_5, x_4, x_3, x_2, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_4 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__0);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__1);
l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2 = _init_l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2();
lean_mark_persistent(l_List_foldl___at___Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1_spec__2___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__0);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__1);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__2);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__3);
l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4 = _init_l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName_spec__0_spec__1___redArg___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__0);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace_spec__0___redArg___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__0);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__12);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__13);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__14);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__15);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__16);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__17);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__18);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__0);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5);
l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6 = _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6);
if (builtin) {res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_0__Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
