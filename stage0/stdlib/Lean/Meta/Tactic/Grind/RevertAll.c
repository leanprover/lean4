// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RevertAll
// Imports: Lean.Meta.Tactic.Util
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_revertAll___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revertAll___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revertAll___lambda__2___closed__4;
static lean_object* l_Lean_MVarId_revertAll___lambda__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revertAll___closed__1;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revertAll___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revertAll___lambda__2___closed__5;
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
lean_inc(x_11);
x_12 = l_Lean_FVarId_getDecl(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_isAuxDecl(x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = l_Lean_Expr_fvar___override(x_11);
x_17 = lean_array_push(x_4, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_17;
x_9 = x_14;
goto _start;
}
else
{
size_t x_21; size_t x_22; 
lean_dec(x_11);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_9 = x_14;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
static lean_object* _init_l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_le(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_usize_of_nat(x_2);
x_17 = lean_usize_of_nat(x_3);
x_18 = l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2(x_1, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = l_Lean_Expr_getAppFn(x_8);
x_10 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Lean_MVarId_setTag(x_10, x_1, x_3, x_4, x_5, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_revertAll___lambda__2___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MVarId_revertAll___lambda__2___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create binder due to failure when reverting variable dependencies", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_revertAll___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = l_Lean_LocalContext_getFVarIds(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_14 = l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1(x_11, x_13, x_12, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_32; lean_object* x_45; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_1);
x_21 = l_Lean_MVarId_setKind(x_1, x_20, x_3, x_4, x_5, x_6, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_73 = lean_st_ref_get(x_6, x_22);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_st_ref_get(x_4, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_get(x_6, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 2);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_6, x_83);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_environment_main_module(x_76);
lean_ctor_set(x_85, 1, x_10);
lean_ctor_set(x_85, 0, x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Lean_MVarId_revertAll___lambda__2___closed__3;
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_84);
lean_ctor_set(x_92, 3, x_91);
x_93 = 1;
lean_inc(x_1);
x_94 = l_Lean_MetavarContext_revert(x_15, x_1, x_93, x_85, x_92);
lean_dec(x_85);
lean_dec(x_15);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 2);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_st_ref_take(x_4, x_88);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_101, 0);
lean_dec(x_104);
lean_ctor_set(x_101, 0, x_97);
x_105 = lean_st_ref_set(x_4, x_101, x_102);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_st_ref_take(x_6, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_108, 2);
lean_dec(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_dec(x_112);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 1, x_98);
x_113 = lean_st_ref_set(x_6, x_108, x_109);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_96);
x_45 = x_113;
goto block_72;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_96);
lean_ctor_set(x_117, 1, x_116);
x_45 = x_117;
goto block_72;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_108, 0);
x_119 = lean_ctor_get(x_108, 3);
x_120 = lean_ctor_get(x_108, 4);
x_121 = lean_ctor_get(x_108, 5);
x_122 = lean_ctor_get(x_108, 6);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_108);
x_123 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_98);
lean_ctor_set(x_123, 2, x_99);
lean_ctor_set(x_123, 3, x_119);
lean_ctor_set(x_123, 4, x_120);
lean_ctor_set(x_123, 5, x_121);
lean_ctor_set(x_123, 6, x_122);
x_124 = lean_st_ref_set(x_6, x_123, x_109);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_96);
lean_ctor_set(x_127, 1, x_125);
x_45 = x_127;
goto block_72;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_128 = lean_ctor_get(x_101, 1);
x_129 = lean_ctor_get(x_101, 2);
x_130 = lean_ctor_get(x_101, 3);
x_131 = lean_ctor_get(x_101, 4);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_101);
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_97);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set(x_132, 4, x_131);
x_133 = lean_st_ref_set(x_4, x_132, x_102);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_take(x_6, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 5);
lean_inc(x_141);
x_142 = lean_ctor_get(x_136, 6);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 lean_ctor_release(x_136, 4);
 lean_ctor_release(x_136, 5);
 lean_ctor_release(x_136, 6);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 7, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_98);
lean_ctor_set(x_144, 2, x_99);
lean_ctor_set(x_144, 3, x_139);
lean_ctor_set(x_144, 4, x_140);
lean_ctor_set(x_144, 5, x_141);
lean_ctor_set(x_144, 6, x_142);
x_145 = lean_st_ref_set(x_6, x_144, x_137);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_96);
lean_ctor_set(x_148, 1, x_146);
x_45 = x_148;
goto block_72;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_149 = lean_ctor_get(x_94, 1);
lean_inc(x_149);
lean_dec(x_94);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 2);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_st_ref_take(x_4, x_88);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = !lean_is_exclusive(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_157 = lean_ctor_get(x_154, 0);
lean_dec(x_157);
lean_ctor_set(x_154, 0, x_150);
x_158 = lean_st_ref_set(x_4, x_154, x_155);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_st_ref_take(x_6, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_161, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_dec(x_165);
lean_ctor_set(x_161, 2, x_152);
lean_ctor_set(x_161, 1, x_151);
x_166 = lean_st_ref_set(x_6, x_161, x_162);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_MVarId_revertAll___lambda__2___closed__5;
x_169 = l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(x_168, x_3, x_4, x_5, x_6, x_167);
x_45 = x_169;
goto block_72;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_170 = lean_ctor_get(x_161, 0);
x_171 = lean_ctor_get(x_161, 3);
x_172 = lean_ctor_get(x_161, 4);
x_173 = lean_ctor_get(x_161, 5);
x_174 = lean_ctor_get(x_161, 6);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_161);
x_175 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_151);
lean_ctor_set(x_175, 2, x_152);
lean_ctor_set(x_175, 3, x_171);
lean_ctor_set(x_175, 4, x_172);
lean_ctor_set(x_175, 5, x_173);
lean_ctor_set(x_175, 6, x_174);
x_176 = lean_st_ref_set(x_6, x_175, x_162);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_MVarId_revertAll___lambda__2___closed__5;
x_179 = l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(x_178, x_3, x_4, x_5, x_6, x_177);
x_45 = x_179;
goto block_72;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_180 = lean_ctor_get(x_154, 1);
x_181 = lean_ctor_get(x_154, 2);
x_182 = lean_ctor_get(x_154, 3);
x_183 = lean_ctor_get(x_154, 4);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_154);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_150);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_181);
lean_ctor_set(x_184, 3, x_182);
lean_ctor_set(x_184, 4, x_183);
x_185 = lean_st_ref_set(x_4, x_184, x_155);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_st_ref_take(x_6, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 5);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 6);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 lean_ctor_release(x_188, 6);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(0, 7, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_151);
lean_ctor_set(x_196, 2, x_152);
lean_ctor_set(x_196, 3, x_191);
lean_ctor_set(x_196, 4, x_192);
lean_ctor_set(x_196, 5, x_193);
lean_ctor_set(x_196, 6, x_194);
x_197 = lean_st_ref_set(x_6, x_196, x_189);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_Lean_MVarId_revertAll___lambda__2___closed__5;
x_200 = l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(x_199, x_3, x_4, x_5, x_6, x_198);
x_45 = x_200;
goto block_72;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_85, 0);
x_202 = lean_ctor_get(x_85, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_85);
x_203 = lean_environment_main_module(x_76);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_10);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_206 = l_Lean_MVarId_revertAll___lambda__2___closed__3;
x_207 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_207, 0, x_80);
lean_ctor_set(x_207, 1, x_205);
lean_ctor_set(x_207, 2, x_84);
lean_ctor_set(x_207, 3, x_206);
x_208 = 1;
lean_inc(x_1);
x_209 = l_Lean_MetavarContext_revert(x_15, x_1, x_208, x_204, x_207);
lean_dec(x_204);
lean_dec(x_15);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 2);
lean_inc(x_214);
lean_dec(x_210);
x_215 = lean_st_ref_take(x_4, x_202);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 lean_ctor_release(x_216, 4);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_212);
lean_ctor_set(x_223, 1, x_218);
lean_ctor_set(x_223, 2, x_219);
lean_ctor_set(x_223, 3, x_220);
lean_ctor_set(x_223, 4, x_221);
x_224 = lean_st_ref_set(x_4, x_223, x_217);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_take(x_6, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 4);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 5);
lean_inc(x_232);
x_233 = lean_ctor_get(x_227, 6);
lean_inc(x_233);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 lean_ctor_release(x_227, 4);
 lean_ctor_release(x_227, 5);
 lean_ctor_release(x_227, 6);
 x_234 = x_227;
} else {
 lean_dec_ref(x_227);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(0, 7, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_213);
lean_ctor_set(x_235, 2, x_214);
lean_ctor_set(x_235, 3, x_230);
lean_ctor_set(x_235, 4, x_231);
lean_ctor_set(x_235, 5, x_232);
lean_ctor_set(x_235, 6, x_233);
x_236 = lean_st_ref_set(x_6, x_235, x_228);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_211);
lean_ctor_set(x_239, 1, x_237);
x_45 = x_239;
goto block_72;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_240 = lean_ctor_get(x_209, 1);
lean_inc(x_240);
lean_dec(x_209);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 2);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_st_ref_take(x_4, x_202);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_245, 4);
lean_inc(x_250);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 lean_ctor_release(x_245, 3);
 lean_ctor_release(x_245, 4);
 x_251 = x_245;
} else {
 lean_dec_ref(x_245);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 5, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_247);
lean_ctor_set(x_252, 2, x_248);
lean_ctor_set(x_252, 3, x_249);
lean_ctor_set(x_252, 4, x_250);
x_253 = lean_st_ref_set(x_4, x_252, x_246);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_255 = lean_st_ref_take(x_6, x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_256, 5);
lean_inc(x_261);
x_262 = lean_ctor_get(x_256, 6);
lean_inc(x_262);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 lean_ctor_release(x_256, 4);
 lean_ctor_release(x_256, 5);
 lean_ctor_release(x_256, 6);
 x_263 = x_256;
} else {
 lean_dec_ref(x_256);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 7, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_258);
lean_ctor_set(x_264, 1, x_242);
lean_ctor_set(x_264, 2, x_243);
lean_ctor_set(x_264, 3, x_259);
lean_ctor_set(x_264, 4, x_260);
lean_ctor_set(x_264, 5, x_261);
lean_ctor_set(x_264, 6, x_262);
x_265 = lean_st_ref_set(x_6, x_264, x_257);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_267 = l_Lean_MVarId_revertAll___lambda__2___closed__5;
x_268 = l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(x_267, x_3, x_4, x_5, x_6, x_266);
x_45 = x_268;
goto block_72;
}
}
block_31:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_MVarId_revertAll___lambda__1(x_18, x_24, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_3);
lean_dec(x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
block_44:
{
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_35);
x_23 = x_32;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_23 = x_39;
goto block_31;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
x_23 = x_32;
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_23 = x_43;
goto block_31;
}
}
}
block_72:
{
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = 2;
x_49 = l_Lean_MVarId_setKind(x_1, x_48, x_3, x_4, x_5, x_6, x_47);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_45, 1, x_51);
lean_ctor_set(x_49, 0, x_45);
x_32 = x_49;
goto block_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_45, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
x_32 = x_54;
goto block_44;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = 2;
x_58 = l_Lean_MVarId_setKind(x_1, x_57, x_3, x_4, x_5, x_6, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_32 = x_63;
goto block_44;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_dec(x_45);
x_66 = 2;
x_67 = l_Lean_MVarId_setKind(x_1, x_66, x_3, x_4, x_5, x_6, x_65);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_64);
x_32 = x_67;
goto block_44;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
x_32 = x_71;
goto block_44;
}
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_17);
if (x_269 == 0)
{
return x_17;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_17, 0);
x_271 = lean_ctor_get(x_17, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_17);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_273 = !lean_is_exclusive(x_14);
if (x_273 == 0)
{
return x_14;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_14, 0);
x_275 = lean_ctor_get(x_14, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_14);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_3);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_8);
if (x_277 == 0)
{
return x_8;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_8, 0);
x_279 = lean_ctor_get(x_8, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_8);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("revertAll", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revertAll___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_revertAll___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_revertAll___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lambda__2___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_revertAll___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_revertAll___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_revertAll___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_revertAll___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1 = _init_l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1();
lean_mark_persistent(l_Array_filterMapM___at_Lean_MVarId_revertAll___spec__1___closed__1);
l_Lean_MVarId_revertAll___lambda__2___closed__1 = _init_l_Lean_MVarId_revertAll___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_revertAll___lambda__2___closed__1);
l_Lean_MVarId_revertAll___lambda__2___closed__2 = _init_l_Lean_MVarId_revertAll___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_revertAll___lambda__2___closed__2);
l_Lean_MVarId_revertAll___lambda__2___closed__3 = _init_l_Lean_MVarId_revertAll___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_revertAll___lambda__2___closed__3);
l_Lean_MVarId_revertAll___lambda__2___closed__4 = _init_l_Lean_MVarId_revertAll___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_revertAll___lambda__2___closed__4);
l_Lean_MVarId_revertAll___lambda__2___closed__5 = _init_l_Lean_MVarId_revertAll___lambda__2___closed__5();
lean_mark_persistent(l_Lean_MVarId_revertAll___lambda__2___closed__5);
l_Lean_MVarId_revertAll___closed__1 = _init_l_Lean_MVarId_revertAll___closed__1();
lean_mark_persistent(l_Lean_MVarId_revertAll___closed__1);
l_Lean_MVarId_revertAll___closed__2 = _init_l_Lean_MVarId_revertAll___closed__2();
lean_mark_persistent(l_Lean_MVarId_revertAll___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
