// Lean compiler output
// Module: Lean.Elab.Tactic.Injection
// Imports: Init Lean.Meta.Tactic.Injection Lean.Elab.Tactic.ElabTerm
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
extern lean_object* l_Lean_Meta_injectionCore___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___boxed(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInjection(lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInjection___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInjection___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Syntax_getId(x_4);
lean_dec(x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_6 = l_Array_toList___rarg(x_5);
lean_dec(x_5);
x_7 = l_List_map___main___at___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___spec__1(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many identifiers provided, unused: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_injectionCore___closed__2;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_1, x_13, x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
x_22 = l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds(x_1, x_21, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Tactic_elabAsFVar(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l___private_Lean_Elab_Tactic_Injection_1__getInjectionNewIds(x_18);
lean_dec(x_18);
lean_inc(x_4);
x_20 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_List_isEmpty___rarg(x_19);
lean_inc(x_19);
lean_inc(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___lambda__1___boxed), 8, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 5);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_5);
lean_inc(x_23);
x_28 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_23, x_6, x_7, x_8, x_9, x_22);
if (x_25 == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_injection___boxed), 9, 4);
lean_closure_set(x_33, 0, x_23);
lean_closure_set(x_33, 1, x_15);
lean_closure_set(x_33, 2, x_19);
lean_closure_set(x_33, 3, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_26);
x_35 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 5);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_5);
x_38 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_27);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 4);
lean_inc(x_40);
lean_dec(x_29);
x_41 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_39, x_40, x_38, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_28, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_dec(x_28);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_injection___boxed), 9, 4);
lean_closure_set(x_58, 0, x_23);
lean_closure_set(x_58, 1, x_15);
lean_closure_set(x_58, 2, x_19);
lean_closure_set(x_58, 3, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_26);
x_60 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_61 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_61, 0, x_59);
lean_closure_set(x_61, 1, x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 5);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_2);
lean_closure_set(x_62, 2, x_3);
lean_closure_set(x_62, 3, x_4);
lean_closure_set(x_62, 4, x_5);
x_63 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_27);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 4);
lean_inc(x_65);
lean_dec(x_54);
x_66 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_64, x_65, x_63, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_28);
if (x_75 == 0)
{
return x_28;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_28, 0);
x_77 = lean_ctor_get(x_28, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_28);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_20);
if (x_79 == 0)
{
return x_20;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_20, 0);
x_81 = lean_ctor_get(x_20, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_20);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
return x_14;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_14, 0);
x_85 = lean_ctor_get(x_14, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_14);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalInjection___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalInjection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalInjection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_2 = l_Lean_Meta_injectionCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalInjection___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalInjection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Injection(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1 = _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__1);
l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2 = _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__2);
l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3 = _init_l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Injection_2__checkUnusedIds___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalInjection___closed__2);
res = l___regBuiltin_Lean_Elab_Tactic_evalInjection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
