// Lean compiler output
// Module: Lean.Elab.Tactic.Generalize
// Imports: Init Lean.Meta.Tactic.Generalize Lean.Meta.Check Lean.Meta.Tactic.Intro Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Location
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
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_MVarId_generalizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3;
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = l_Lean_Syntax_getArg(x_15, x_16);
x_19 = l_Lean_Syntax_isNone(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
x_22 = lean_box(0);
x_23 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_Tactic_elabTerm(x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (x_19 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Syntax_getArg(x_18, x_16);
lean_dec(x_18);
x_28 = l_Lean_Syntax_getId(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_15, x_30);
lean_dec(x_15);
x_32 = l_Lean_Syntax_getId(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
x_35 = 1;
x_36 = lean_usize_add(x_2, x_35);
x_37 = lean_array_uset(x_17, x_2, x_34);
x_2 = x_36;
x_3 = x_37;
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_unsigned_to_nat(3u);
x_46 = l_Lean_Syntax_getArg(x_15, x_45);
lean_dec(x_15);
x_47 = l_Lean_Syntax_getId(x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_22);
x_50 = 1;
x_51 = lean_usize_add(x_2, x_50);
x_52 = lean_array_uset(x_17, x_2, x_49);
x_2 = x_51;
x_3 = x_52;
x_12 = x_44;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
return x_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_24, 0);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_MVarId_generalizeHyp(x_13, x_1, x_2, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_replaceMainGoal(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lambda__1), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Elab_Tactic_withMainContext___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_4, x_17);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_expandOptLocation(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
x_21 = l_Lean_LocalContext_getFVarIds(x_20);
x_22 = l_Lean_Elab_Tactic_evalGeneralize___lambda__2(x_15, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Tactic_getFVarIds(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Tactic_evalGeneralize___lambda__2(x_15, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getSepArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = lean_box_usize(x_15);
x_17 = l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1;
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lambda__3___boxed), 13, 4);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_1);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalGeneralize___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_Tactic_evalGeneralize___lambda__3(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("generalize", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalGeneralize", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2;
x_4 = lean_unsigned_to_nat(21u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(65u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5;
x_4 = lean_unsigned_to_nat(65u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1 = _init_l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__7);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__8);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize___closed__10);
res = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
