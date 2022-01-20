// Lean compiler output
// Module: Lean.Compiler.IR.NormIds
// Imports: Init Lean.Compiler.IR.Basic
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_NormalizeIds_normFnBody___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_Std_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_1, x_4);
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_UniqueIds_checkId(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_3, x_3);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_15 = l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_13, x_14, x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_UniqueIds_checkFnBody(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_UniqueIds_checkId(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_1 = x_4;
x_2 = x_12;
goto _start;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_IR_UniqueIds_checkId(x_14, x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_18);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_IR_UniqueIds_checkParams(x_15, x_24);
lean_dec(x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_1 = x_16;
x_2 = x_32;
goto _start;
}
}
}
case 10:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_array_get_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_34);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_35, x_35);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_34);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_47 = l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1(x_34, x_45, x_46, x_2);
lean_dec(x_34);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = 1;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
lean_dec(x_59);
x_60 = 0;
x_61 = lean_box(x_60);
lean_ctor_set(x_47, 0, x_61);
return x_47;
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_dec(x_47);
x_63 = 0;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
}
}
default: 
{
uint8_t x_66; 
x_66 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_67;
goto _start;
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_2);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_UniqueIds_checkFnBody___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_UniqueIds_checkDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_UniqueIds_checkParams(x_3, x_2);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_IR_UniqueIds_checkFnBody(x_4, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_IR_UniqueIds_checkParams(x_14, x_2);
lean_dec(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_uniqueIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_IR_UniqueIds_checkDecl(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normIndex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_IR_NormalizeIds_normIndex(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_NormalizeIds_normIndex(x_6, x_2);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_IR_NormalizeIds_normArg(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_4, x_5, x_1);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_IR_NormalizeIds_normArgs(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Lean_IR_NormalizeIds_normArgs(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_2);
lean_dec(x_2);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_IR_NormalizeIds_normIndex(x_14, x_2);
lean_dec(x_2);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_2);
lean_dec(x_18);
x_21 = l_Lean_IR_NormalizeIds_normArgs(x_19, x_2);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = l_Lean_IR_NormalizeIds_normIndex(x_22, x_2);
lean_dec(x_22);
x_27 = l_Lean_IR_NormalizeIds_normArgs(x_25, x_2);
x_28 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_24);
return x_28;
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = l_Lean_IR_NormalizeIds_normIndex(x_30, x_2);
lean_dec(x_2);
lean_dec(x_30);
lean_ctor_set(x_1, 1, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = l_Lean_IR_NormalizeIds_normIndex(x_33, x_2);
lean_dec(x_2);
lean_dec(x_33);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 1);
x_38 = l_Lean_IR_NormalizeIds_normIndex(x_37, x_2);
lean_dec(x_2);
lean_dec(x_37);
lean_ctor_set(x_1, 1, x_38);
return x_1;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_1);
x_41 = l_Lean_IR_NormalizeIds_normIndex(x_40, x_2);
lean_dec(x_2);
lean_dec(x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 5:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 2);
x_45 = l_Lean_IR_NormalizeIds_normIndex(x_44, x_2);
lean_dec(x_2);
lean_dec(x_44);
lean_ctor_set(x_1, 2, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_49 = l_Lean_IR_NormalizeIds_normIndex(x_48, x_2);
lean_dec(x_2);
lean_dec(x_48);
x_50 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
}
case 6:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 1);
x_53 = l_Lean_IR_NormalizeIds_normArgs(x_52, x_2);
lean_ctor_set(x_1, 1, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_1);
x_56 = l_Lean_IR_NormalizeIds_normArgs(x_55, x_2);
x_57 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
case 7:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 1);
x_60 = l_Lean_IR_NormalizeIds_normArgs(x_59, x_2);
lean_ctor_set(x_1, 1, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_1);
x_63 = l_Lean_IR_NormalizeIds_normArgs(x_62, x_2);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
case 8:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
x_68 = l_Lean_IR_NormalizeIds_normIndex(x_66, x_2);
lean_dec(x_66);
x_69 = l_Lean_IR_NormalizeIds_normArgs(x_67, x_2);
lean_ctor_set(x_1, 1, x_69);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_72 = l_Lean_IR_NormalizeIds_normIndex(x_70, x_2);
lean_dec(x_70);
x_73 = l_Lean_IR_NormalizeIds_normArgs(x_71, x_2);
x_74 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
case 9:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_1);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_1, 1);
x_77 = l_Lean_IR_NormalizeIds_normIndex(x_76, x_2);
lean_dec(x_2);
lean_dec(x_76);
lean_ctor_set(x_1, 1, x_77);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_80 = l_Lean_IR_NormalizeIds_normIndex(x_79, x_2);
lean_dec(x_2);
lean_dec(x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
case 10:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_1, 0);
x_84 = l_Lean_IR_NormalizeIds_normIndex(x_83, x_2);
lean_dec(x_2);
lean_dec(x_83);
lean_ctor_set(x_1, 0, x_84);
return x_1;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
lean_dec(x_1);
x_86 = l_Lean_IR_NormalizeIds_normIndex(x_85, x_2);
lean_dec(x_2);
lean_dec(x_85);
x_87 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
case 11:
{
lean_dec(x_2);
return x_1;
}
case 12:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_1);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_1, 0);
x_90 = l_Lean_IR_NormalizeIds_normIndex(x_89, x_2);
lean_dec(x_2);
lean_dec(x_89);
lean_ctor_set(x_1, 0, x_90);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_IR_NormalizeIds_normIndex(x_91, x_2);
lean_dec(x_2);
lean_dec(x_91);
x_93 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
default: 
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_1);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_1, 0);
x_96 = l_Lean_IR_NormalizeIds_normIndex(x_95, x_2);
lean_dec(x_2);
lean_dec(x_95);
lean_ctor_set(x_1, 0, x_96);
return x_1;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
lean_dec(x_1);
x_98 = l_Lean_IR_NormalizeIds_normIndex(x_97, x_2);
lean_dec(x_2);
lean_dec(x_97);
x_99 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_inc(x_4);
x_7 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean_apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withVar___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_inc(x_4);
x_7 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean_apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withJP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withJP___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_6);
x_19 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_8, x_3, x_20);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_10, x_5);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
x_5 = x_17;
goto block_13;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_4);
x_5 = x_19;
goto block_13;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(x_1, x_20, x_21, x_3, x_4);
x_5 = x_22;
goto block_13;
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1(x_6, x_9, x_10, x_1);
x_12 = lean_apply_3(x_2, x_11, x_6, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_withParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_withParams___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_withParams___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_instMonadLiftMN(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_instMonadLiftMN___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_11);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_6);
x_19 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_8, x_3, x_20);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_NormalizeIds_normFnBody___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_apply_3(x_1, x_6, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_apply_3(x_1, x_14, x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_apply_3(x_1, x_22, x_3, x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_2, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_apply_3(x_1, x_29, x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_NormalizeIds_normFnBody), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1;
lean_inc(x_4);
x_12 = l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_NormalizeIds_normFnBody___spec__2(x_11, x_8, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_10, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_5 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_8 = l_Lean_IR_NormalizeIds_normExpr(x_6, x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_inc(x_3);
x_11 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_5, x_3);
x_12 = l_Lean_IR_NormalizeIds_normFnBody(x_7, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 0, x_3);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 0, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_2);
x_22 = l_Lean_IR_NormalizeIds_normExpr(x_20, x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_inc(x_3);
x_25 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_18, x_3);
x_26 = l_Lean_IR_NormalizeIds_normFnBody(x_21, x_25, x_24);
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
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
x_59 = lean_array_get_size(x_33);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
lean_inc(x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_3);
x_37 = x_62;
goto block_58;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_59, x_59);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_59);
lean_inc(x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_3);
x_37 = x_64;
goto block_58;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
lean_dec(x_59);
lean_inc(x_2);
x_67 = l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(x_33, x_65, x_66, x_2, x_3);
x_37 = x_67;
goto block_58;
}
}
block_58:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_get_size(x_33);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = 0;
x_43 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1(x_38, x_41, x_42, x_33);
x_44 = l_Lean_IR_NormalizeIds_normFnBody(x_34, x_38, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_46, x_47);
lean_inc(x_46);
x_49 = l_Std_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_32, x_46);
x_50 = l_Lean_IR_NormalizeIds_normFnBody(x_35, x_49, x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
if (lean_is_scalar(x_36)) {
 x_53 = lean_alloc_ctor(1, 4, 0);
} else {
 x_53 = x_36;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
if (lean_is_scalar(x_36)) {
 x_56 = lean_alloc_ctor(1, 4, 0);
} else {
 x_56 = x_36;
}
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
case 2:
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_ctor_get(x_1, 2);
x_71 = lean_ctor_get(x_1, 3);
x_72 = l_Lean_IR_NormalizeIds_normIndex(x_69, x_2);
lean_dec(x_69);
x_73 = l_Lean_IR_NormalizeIds_normArg(x_70, x_2);
x_74 = l_Lean_IR_NormalizeIds_normFnBody(x_71, x_2, x_3);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_1, 2, x_73);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set(x_74, 0, x_1);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
lean_ctor_set(x_1, 3, x_77);
lean_ctor_set(x_1, 2, x_73);
lean_ctor_set(x_1, 0, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 1);
x_82 = lean_ctor_get(x_1, 2);
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_1);
x_84 = l_Lean_IR_NormalizeIds_normIndex(x_80, x_2);
lean_dec(x_80);
x_85 = l_Lean_IR_NormalizeIds_normArg(x_82, x_2);
x_86 = l_Lean_IR_NormalizeIds_normFnBody(x_83, x_2, x_3);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set(x_90, 3, x_87);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
case 3:
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_1);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_1, 0);
x_94 = lean_ctor_get(x_1, 2);
x_95 = l_Lean_IR_NormalizeIds_normIndex(x_93, x_2);
lean_dec(x_93);
x_96 = l_Lean_IR_NormalizeIds_normFnBody(x_94, x_2, x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set(x_96, 0, x_1);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_96);
lean_ctor_set(x_1, 2, x_99);
lean_ctor_set(x_1, 0, x_95);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_1, 0);
x_103 = lean_ctor_get(x_1, 1);
x_104 = lean_ctor_get(x_1, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_1);
x_105 = l_Lean_IR_NormalizeIds_normIndex(x_102, x_2);
lean_dec(x_102);
x_106 = l_Lean_IR_NormalizeIds_normFnBody(x_104, x_2, x_3);
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
x_110 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_107);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
case 4:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_1);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_113 = lean_ctor_get(x_1, 0);
x_114 = lean_ctor_get(x_1, 2);
x_115 = lean_ctor_get(x_1, 3);
x_116 = l_Lean_IR_NormalizeIds_normIndex(x_113, x_2);
lean_dec(x_113);
x_117 = l_Lean_IR_NormalizeIds_normIndex(x_114, x_2);
lean_dec(x_114);
x_118 = l_Lean_IR_NormalizeIds_normFnBody(x_115, x_2, x_3);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_118, 0);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_117);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set(x_118, 0, x_1);
return x_118;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_118, 0);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_118);
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_117);
lean_ctor_set(x_1, 0, x_116);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 1);
x_126 = lean_ctor_get(x_1, 2);
x_127 = lean_ctor_get(x_1, 3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_1);
x_128 = l_Lean_IR_NormalizeIds_normIndex(x_124, x_2);
lean_dec(x_124);
x_129 = l_Lean_IR_NormalizeIds_normIndex(x_126, x_2);
lean_dec(x_126);
x_130 = l_Lean_IR_NormalizeIds_normFnBody(x_127, x_2, x_3);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_125);
lean_ctor_set(x_134, 2, x_129);
lean_ctor_set(x_134, 3, x_131);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
}
case 5:
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_1);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_137 = lean_ctor_get(x_1, 0);
x_138 = lean_ctor_get(x_1, 3);
x_139 = lean_ctor_get(x_1, 5);
x_140 = l_Lean_IR_NormalizeIds_normIndex(x_137, x_2);
lean_dec(x_137);
x_141 = l_Lean_IR_NormalizeIds_normIndex(x_138, x_2);
lean_dec(x_138);
x_142 = l_Lean_IR_NormalizeIds_normFnBody(x_139, x_2, x_3);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_ctor_set(x_1, 5, x_144);
lean_ctor_set(x_1, 3, x_141);
lean_ctor_set(x_1, 0, x_140);
lean_ctor_set(x_142, 0, x_1);
return x_142;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_142, 0);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_142);
lean_ctor_set(x_1, 5, x_145);
lean_ctor_set(x_1, 3, x_141);
lean_ctor_set(x_1, 0, x_140);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_148 = lean_ctor_get(x_1, 0);
x_149 = lean_ctor_get(x_1, 1);
x_150 = lean_ctor_get(x_1, 2);
x_151 = lean_ctor_get(x_1, 3);
x_152 = lean_ctor_get(x_1, 4);
x_153 = lean_ctor_get(x_1, 5);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_1);
x_154 = l_Lean_IR_NormalizeIds_normIndex(x_148, x_2);
lean_dec(x_148);
x_155 = l_Lean_IR_NormalizeIds_normIndex(x_151, x_2);
lean_dec(x_151);
x_156 = l_Lean_IR_NormalizeIds_normFnBody(x_153, x_2, x_3);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_149);
lean_ctor_set(x_160, 2, x_150);
lean_ctor_set(x_160, 3, x_155);
lean_ctor_set(x_160, 4, x_152);
lean_ctor_set(x_160, 5, x_157);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
case 6:
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_1);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_1, 0);
x_164 = lean_ctor_get(x_1, 2);
x_165 = l_Lean_IR_NormalizeIds_normIndex(x_163, x_2);
lean_dec(x_163);
x_166 = l_Lean_IR_NormalizeIds_normFnBody(x_164, x_2, x_3);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_ctor_set(x_1, 2, x_168);
lean_ctor_set(x_1, 0, x_165);
lean_ctor_set(x_166, 0, x_1);
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_166);
lean_ctor_set(x_1, 2, x_169);
lean_ctor_set(x_1, 0, x_165);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_172 = lean_ctor_get(x_1, 0);
x_173 = lean_ctor_get(x_1, 1);
x_174 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_175 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_176 = lean_ctor_get(x_1, 2);
lean_inc(x_176);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_1);
x_177 = l_Lean_IR_NormalizeIds_normIndex(x_172, x_2);
lean_dec(x_172);
x_178 = l_Lean_IR_NormalizeIds_normFnBody(x_176, x_2, x_3);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_182, 0, x_177);
lean_ctor_set(x_182, 1, x_173);
lean_ctor_set(x_182, 2, x_179);
lean_ctor_set_uint8(x_182, sizeof(void*)*3, x_174);
lean_ctor_set_uint8(x_182, sizeof(void*)*3 + 1, x_175);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
case 7:
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_1);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_1, 0);
x_186 = lean_ctor_get(x_1, 2);
x_187 = l_Lean_IR_NormalizeIds_normIndex(x_185, x_2);
lean_dec(x_185);
x_188 = l_Lean_IR_NormalizeIds_normFnBody(x_186, x_2, x_3);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_188, 0);
lean_ctor_set(x_1, 2, x_190);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set(x_188, 0, x_1);
return x_188;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_188, 0);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_188);
lean_ctor_set(x_1, 2, x_191);
lean_ctor_set(x_1, 0, x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_1);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_194 = lean_ctor_get(x_1, 0);
x_195 = lean_ctor_get(x_1, 1);
x_196 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_197 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_198 = lean_ctor_get(x_1, 2);
lean_inc(x_198);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_1);
x_199 = l_Lean_IR_NormalizeIds_normIndex(x_194, x_2);
lean_dec(x_194);
x_200 = l_Lean_IR_NormalizeIds_normFnBody(x_198, x_2, x_3);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_195);
lean_ctor_set(x_204, 2, x_201);
lean_ctor_set_uint8(x_204, sizeof(void*)*3, x_196);
lean_ctor_set_uint8(x_204, sizeof(void*)*3 + 1, x_197);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
}
case 8:
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_1);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_1, 0);
x_208 = lean_ctor_get(x_1, 1);
x_209 = l_Lean_IR_NormalizeIds_normIndex(x_207, x_2);
lean_dec(x_207);
x_210 = l_Lean_IR_NormalizeIds_normFnBody(x_208, x_2, x_3);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_210, 0);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set(x_1, 0, x_209);
lean_ctor_set(x_210, 0, x_1);
return x_210;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_210, 0);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_210);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_209);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_1, 0);
x_217 = lean_ctor_get(x_1, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_1);
x_218 = l_Lean_IR_NormalizeIds_normIndex(x_216, x_2);
lean_dec(x_216);
x_219 = l_Lean_IR_NormalizeIds_normFnBody(x_217, x_2, x_3);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
}
case 9:
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_1);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_1, 1);
x_227 = l_Lean_IR_NormalizeIds_normFnBody(x_226, x_2, x_3);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_227, 0);
lean_ctor_set(x_1, 1, x_229);
lean_ctor_set(x_227, 0, x_1);
return x_227;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_227, 0);
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_227);
lean_ctor_set(x_1, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_1);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_ctor_get(x_1, 0);
x_234 = lean_ctor_get(x_1, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_1);
x_235 = l_Lean_IR_NormalizeIds_normFnBody(x_234, x_2, x_3);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_236);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
case 10:
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_1);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; size_t x_246; size_t x_247; lean_object* x_248; uint8_t x_249; 
x_242 = lean_ctor_get(x_1, 1);
x_243 = lean_ctor_get(x_1, 3);
x_244 = l_Lean_IR_NormalizeIds_normIndex(x_242, x_2);
lean_dec(x_242);
x_245 = lean_array_get_size(x_243);
x_246 = lean_usize_of_nat(x_245);
lean_dec(x_245);
x_247 = 0;
x_248 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3(x_246, x_247, x_243, x_2, x_3);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_248, 0);
lean_ctor_set(x_1, 3, x_250);
lean_ctor_set(x_1, 1, x_244);
lean_ctor_set(x_248, 0, x_1);
return x_248;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_248, 0);
x_252 = lean_ctor_get(x_248, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_248);
lean_ctor_set(x_1, 3, x_251);
lean_ctor_set(x_1, 1, x_244);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_1);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; size_t x_260; size_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_254 = lean_ctor_get(x_1, 0);
x_255 = lean_ctor_get(x_1, 1);
x_256 = lean_ctor_get(x_1, 2);
x_257 = lean_ctor_get(x_1, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_1);
x_258 = l_Lean_IR_NormalizeIds_normIndex(x_255, x_2);
lean_dec(x_255);
x_259 = lean_array_get_size(x_257);
x_260 = lean_usize_of_nat(x_259);
lean_dec(x_259);
x_261 = 0;
x_262 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3(x_260, x_261, x_257, x_2, x_3);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_266, 0, x_254);
lean_ctor_set(x_266, 1, x_258);
lean_ctor_set(x_266, 2, x_256);
lean_ctor_set(x_266, 3, x_263);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
}
case 11:
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_1);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_1, 0);
x_270 = l_Lean_IR_NormalizeIds_normArg(x_269, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_270);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_1);
lean_ctor_set(x_271, 1, x_3);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_1, 0);
lean_inc(x_272);
lean_dec(x_1);
x_273 = l_Lean_IR_NormalizeIds_normArg(x_272, x_2);
lean_dec(x_2);
x_274 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_3);
return x_275;
}
}
case 12:
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_1);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_1, 0);
x_278 = lean_ctor_get(x_1, 1);
x_279 = l_Lean_IR_NormalizeIds_normIndex(x_277, x_2);
lean_dec(x_277);
x_280 = l_Lean_IR_NormalizeIds_normArgs(x_278, x_2);
lean_ctor_set(x_1, 1, x_280);
lean_ctor_set(x_1, 0, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_1);
lean_ctor_set(x_281, 1, x_3);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_1, 0);
x_283 = lean_ctor_get(x_1, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_1);
x_284 = l_Lean_IR_NormalizeIds_normIndex(x_282, x_2);
lean_dec(x_282);
x_285 = l_Lean_IR_NormalizeIds_normArgs(x_283, x_2);
x_286 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_3);
return x_287;
}
}
default: 
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_2);
x_288 = lean_box(13);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_3);
return x_289;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_NormalizeIds_normDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_18 = lean_array_get_size(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
x_6 = x_21;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
x_6 = x_23;
goto block_17;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_IR_NormalizeIds_withParams___spec__2(x_4, x_24, x_25, x_2, x_3);
lean_dec(x_4);
x_6 = x_26;
goto block_17;
}
}
block_17:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_NormalizeIds_normFnBody(x_5, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_Decl_updateBody_x21(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_IR_Decl_updateBody_x21(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_normalizeIds(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_IR_NormalizeIds_normDecl(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_6, 0, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_array_uset(x_8, x_3, x_18);
x_3 = x_10;
x_4 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_4, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_MapVars_mapArgs(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_Lean_IR_MapVars_mapArgs(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_2, 1, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_20 = lean_apply_1(x_1, x_18);
x_21 = l_Lean_IR_MapVars_mapArgs(x_1, x_19);
lean_ctor_set(x_2, 2, x_21);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_1);
x_26 = lean_apply_1(x_1, x_22);
x_27 = l_Lean_IR_MapVars_mapArgs(x_1, x_25);
x_28 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_24);
return x_28;
}
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_apply_1(x_1, x_30);
lean_ctor_set(x_2, 1, x_31);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_apply_1(x_1, x_33);
x_35 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_apply_1(x_1, x_37);
lean_ctor_set(x_2, 1, x_38);
return x_2;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_apply_1(x_1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 5:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_apply_1(x_1, x_44);
lean_ctor_set(x_2, 2, x_45);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_49 = lean_apply_1(x_1, x_48);
x_50 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
}
case 6:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = l_Lean_IR_MapVars_mapArgs(x_1, x_52);
lean_ctor_set(x_2, 1, x_53);
return x_2;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_56 = l_Lean_IR_MapVars_mapArgs(x_1, x_55);
x_57 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
case 7:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_2, 1);
x_60 = l_Lean_IR_MapVars_mapArgs(x_1, x_59);
lean_ctor_set(x_2, 1, x_60);
return x_2;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = l_Lean_IR_MapVars_mapArgs(x_1, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
case 8:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_68 = lean_apply_1(x_1, x_66);
x_69 = l_Lean_IR_MapVars_mapArgs(x_1, x_67);
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_68);
return x_2;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_2);
lean_inc(x_1);
x_72 = lean_apply_1(x_1, x_70);
x_73 = l_Lean_IR_MapVars_mapArgs(x_1, x_71);
x_74 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
case 9:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_2, 1);
x_77 = lean_apply_1(x_1, x_76);
lean_ctor_set(x_2, 1, x_77);
return x_2;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_2);
x_80 = lean_apply_1(x_1, x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
case 10:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_apply_1(x_1, x_83);
lean_ctor_set(x_2, 0, x_84);
return x_2;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_apply_1(x_1, x_85);
x_87 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
case 11:
{
lean_dec(x_1);
return x_2;
}
case 12:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_apply_1(x_1, x_89);
lean_ctor_set(x_2, 0, x_90);
return x_2;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
lean_dec(x_2);
x_92 = lean_apply_1(x_1, x_91);
x_93 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
default: 
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_apply_1(x_1, x_95);
lean_ctor_set(x_2, 0, x_96);
return x_2;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_apply_1(x_1, x_97);
x_99 = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_13 = l_Lean_IR_MapVars_mapFnBody(x_1, x_12);
lean_ctor_set(x_6, 1, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_18 = l_Lean_IR_MapVars_mapFnBody(x_1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_uset(x_8, x_3, x_19);
x_3 = x_10;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_1);
x_24 = l_Lean_IR_MapVars_mapFnBody(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
lean_inc(x_1);
x_28 = l_Lean_IR_MapVars_mapFnBody(x_1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_10;
x_4 = x_30;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_MapVars_mapFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_6 = l_Lean_IR_MapVars_mapExpr(x_1, x_4);
x_7 = l_Lean_IR_MapVars_mapFnBody(x_1, x_5);
lean_ctor_set(x_2, 3, x_7);
lean_ctor_set(x_2, 2, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_IR_MapVars_mapExpr(x_1, x_10);
x_13 = l_Lean_IR_MapVars_mapFnBody(x_1, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_18 = l_Lean_IR_MapVars_mapFnBody(x_1, x_16);
x_19 = l_Lean_IR_MapVars_mapFnBody(x_1, x_17);
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_IR_MapVars_mapFnBody(x_1, x_22);
x_25 = l_Lean_IR_MapVars_mapFnBody(x_1, x_23);
x_26 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
}
case 2:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_31 = lean_apply_1(x_1, x_28);
lean_inc(x_1);
x_32 = l_Lean_IR_MapVars_mapFnBody(x_1, x_30);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_apply_1(x_1, x_34);
lean_ctor_set(x_29, 0, x_35);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_apply_1(x_1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 2, x_38);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean_dec(x_1);
lean_ctor_set(x_2, 3, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
lean_inc(x_1);
x_43 = lean_apply_1(x_1, x_39);
lean_inc(x_1);
x_44 = l_Lean_IR_MapVars_mapFnBody(x_1, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_46 = x_41;
} else {
 lean_dec_ref(x_41);
 x_46 = lean_box(0);
}
x_47 = lean_apply_1(x_1, x_45);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_44);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_44);
return x_50;
}
}
}
case 3:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_54 = lean_apply_1(x_1, x_52);
x_55 = l_Lean_IR_MapVars_mapFnBody(x_1, x_53);
lean_ctor_set(x_2, 2, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
lean_inc(x_1);
x_59 = lean_apply_1(x_1, x_56);
x_60 = l_Lean_IR_MapVars_mapFnBody(x_1, x_58);
x_61 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_60);
return x_61;
}
}
case 4:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_66 = lean_apply_1(x_1, x_63);
lean_inc(x_1);
x_67 = lean_apply_1(x_1, x_64);
x_68 = l_Lean_IR_MapVars_mapFnBody(x_1, x_65);
lean_ctor_set(x_2, 3, x_68);
lean_ctor_set(x_2, 2, x_67);
lean_ctor_set(x_2, 0, x_66);
return x_2;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
lean_inc(x_1);
x_73 = lean_apply_1(x_1, x_69);
lean_inc(x_1);
x_74 = lean_apply_1(x_1, x_71);
x_75 = l_Lean_IR_MapVars_mapFnBody(x_1, x_72);
x_76 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
return x_76;
}
}
case 5:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 3);
x_80 = lean_ctor_get(x_2, 5);
lean_inc(x_1);
x_81 = lean_apply_1(x_1, x_78);
lean_inc(x_1);
x_82 = lean_apply_1(x_1, x_79);
x_83 = l_Lean_IR_MapVars_mapFnBody(x_1, x_80);
lean_ctor_set(x_2, 5, x_83);
lean_ctor_set(x_2, 3, x_82);
lean_ctor_set(x_2, 0, x_81);
return x_2;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
x_87 = lean_ctor_get(x_2, 3);
x_88 = lean_ctor_get(x_2, 4);
x_89 = lean_ctor_get(x_2, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_2);
lean_inc(x_1);
x_90 = lean_apply_1(x_1, x_84);
lean_inc(x_1);
x_91 = lean_apply_1(x_1, x_87);
x_92 = l_Lean_IR_MapVars_mapFnBody(x_1, x_89);
x_93 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_92);
return x_93;
}
}
case 6:
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_97 = lean_apply_1(x_1, x_95);
x_98 = l_Lean_IR_MapVars_mapFnBody(x_1, x_96);
lean_ctor_set(x_2, 2, x_98);
lean_ctor_set(x_2, 0, x_97);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
x_101 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
lean_inc(x_1);
x_104 = lean_apply_1(x_1, x_99);
x_105 = l_Lean_IR_MapVars_mapFnBody(x_1, x_103);
x_106 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*3 + 1, x_102);
return x_106;
}
}
case 7:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_2);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_110 = lean_apply_1(x_1, x_108);
x_111 = l_Lean_IR_MapVars_mapFnBody(x_1, x_109);
lean_ctor_set(x_2, 2, x_111);
lean_ctor_set(x_2, 0, x_110);
return x_2;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
x_114 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_115 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_116 = lean_ctor_get(x_2, 2);
lean_inc(x_116);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_2);
lean_inc(x_1);
x_117 = lean_apply_1(x_1, x_112);
x_118 = l_Lean_IR_MapVars_mapFnBody(x_1, x_116);
x_119 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*3 + 1, x_115);
return x_119;
}
}
case 8:
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_2);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_123 = lean_apply_1(x_1, x_121);
x_124 = l_Lean_IR_MapVars_mapFnBody(x_1, x_122);
lean_ctor_set(x_2, 1, x_124);
lean_ctor_set(x_2, 0, x_123);
return x_2;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_2, 0);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_2);
lean_inc(x_1);
x_127 = lean_apply_1(x_1, x_125);
x_128 = l_Lean_IR_MapVars_mapFnBody(x_1, x_126);
x_129 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
case 9:
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_2);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_2, 1);
x_132 = l_Lean_IR_MapVars_mapFnBody(x_1, x_131);
lean_ctor_set(x_2, 1, x_132);
return x_2;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_2, 0);
x_134 = lean_ctor_get(x_2, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_2);
x_135 = l_Lean_IR_MapVars_mapFnBody(x_1, x_134);
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
case 10:
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_2, 1);
x_139 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_140 = lean_apply_1(x_1, x_138);
x_141 = lean_array_get_size(x_139);
x_142 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_143 = 0;
x_144 = l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1(x_1, x_142, x_143, x_139);
lean_ctor_set(x_2, 3, x_144);
lean_ctor_set(x_2, 1, x_140);
return x_2;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; 
x_145 = lean_ctor_get(x_2, 0);
x_146 = lean_ctor_get(x_2, 1);
x_147 = lean_ctor_get(x_2, 2);
x_148 = lean_ctor_get(x_2, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_2);
lean_inc(x_1);
x_149 = lean_apply_1(x_1, x_146);
x_150 = lean_array_get_size(x_148);
x_151 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_152 = 0;
x_153 = l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1(x_1, x_151, x_152, x_148);
x_154 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_153);
return x_154;
}
}
case 11:
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_2);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_apply_1(x_1, x_158);
lean_ctor_set(x_156, 0, x_159);
return x_2;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_apply_1(x_1, x_160);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_2, 0, x_162);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
lean_dec(x_2);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_apply_1(x_1, x_164);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
else
{
lean_object* x_169; 
lean_dec(x_1);
x_169 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_169, 0, x_163);
return x_169;
}
}
}
case 12:
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_2);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_2, 1);
x_172 = l_Lean_IR_MapVars_mapArgs(x_1, x_171);
lean_ctor_set(x_2, 1, x_172);
return x_2;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_2, 0);
x_174 = lean_ctor_get(x_2, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_2);
x_175 = l_Lean_IR_MapVars_mapArgs(x_1, x_174);
x_176 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
default: 
{
lean_object* x_177; 
lean_dec(x_1);
x_177 = lean_box(13);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_MapVars_mapFnBody___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_mapVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_replaceVar___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_IR_MapVars_mapFnBody(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_replaceVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_FnBody_replaceVar___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_IR_NormalizeIds_normFnBody___spec__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
