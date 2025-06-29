// Lean compiler output
// Module: Lean.Compiler.IR.ResetReuse
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.LiveVars Lean.Compiler.IR.Format
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___redArg(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_hasLiveVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuseCore(lean_object*, uint8_t);
lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_R(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_collectResets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuseCore___boxed(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_instBEqVarId___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; uint8_t x_21; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_21 = lean_nat_dec_eq(x_5, x_9);
if (x_21 == 0)
{
x_17 = x_21;
goto block_20;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_6, x_10);
x_17 = x_22;
goto block_20;
}
block_16:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_13; 
x_13 = lean_name_eq(x_12, x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_name_eq(x_12, x_14);
return x_15;
}
}
block_20:
{
if (x_17 == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_7, x_11);
if (x_18 == 0)
{
return x_18;
}
else
{
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
x_12 = x_4;
goto block_16;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_4, 0);
x_12 = x_19;
goto block_16;
}
}
else
{
return x_3;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_6, x_5, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_1);
x_19 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_18);
lean_ctor_set(x_8, 1, x_19);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
lean_inc(x_1);
x_22 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_11 = x_23;
goto block_16;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_1);
x_26 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_25);
lean_ctor_set(x_8, 0, x_26);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
lean_inc(x_1);
x_28 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_11 = x_29;
goto block_16;
}
}
block_16:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_14 = lean_array_uset(x_10, x_5, x_11);
x_5 = x_13;
x_6 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_12; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_36; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
x_36 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(x_2, x_30, x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_37 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_28);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_25);
lean_ctor_set(x_38, 3, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_25);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
x_32 = x_36;
goto block_35;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_32 = x_43;
goto block_35;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 4, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_28);
return x_34;
}
}
else
{
lean_dec(x_25);
x_12 = x_4;
goto block_24;
}
}
case 1:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_4);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
lean_inc(x_45);
lean_inc(x_1);
x_47 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_45);
lean_inc(x_47);
lean_inc(x_45);
x_48 = l_Lean_IR_FnBody_beq(x_45, x_47);
if (x_48 == 0)
{
lean_dec(x_45);
lean_dec(x_1);
lean_ctor_set(x_4, 2, x_47);
return x_4;
}
else
{
lean_object* x_49; 
lean_dec(x_47);
x_49 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_46);
lean_ctor_set(x_4, 3, x_49);
return x_4;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
x_52 = lean_ctor_get(x_4, 2);
x_53 = lean_ctor_get(x_4, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_4);
lean_inc(x_52);
lean_inc(x_1);
x_54 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_52);
lean_inc(x_54);
lean_inc(x_52);
x_55 = l_Lean_IR_FnBody_beq(x_52, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_1);
x_56 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
x_57 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_53);
x_58 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_57);
return x_58;
}
}
}
case 10:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_4, 3);
x_61 = lean_array_size(x_60);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0(x_1, x_2, x_3, x_61, x_62, x_60);
lean_ctor_set(x_4, 3, x_63);
return x_4;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
x_66 = lean_ctor_get(x_4, 2);
x_67 = lean_ctor_get(x_4, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
x_68 = lean_array_size(x_67);
x_69 = 0;
x_70 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0(x_1, x_2, x_3, x_68, x_69, x_67);
x_71 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
return x_71;
}
}
default: 
{
x_12 = x_4;
goto block_24;
}
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_5, x_7);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_6);
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_9);
return x_10;
}
block_24:
{
uint8_t x_13; 
x_13 = l_Lean_IR_FnBody_isTerminal(x_12);
if (x_13 == 0)
{
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_5 = x_12;
x_6 = x_14;
goto block_11;
}
case 1:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
x_5 = x_12;
x_6 = x_15;
goto block_11;
}
case 2:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 3);
lean_inc(x_16);
x_5 = x_12;
x_6 = x_16;
goto block_11;
}
case 3:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_5 = x_12;
x_6 = x_17;
goto block_11;
}
case 4:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_5 = x_12;
x_6 = x_18;
goto block_11;
}
case 5:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_12, 5);
lean_inc(x_19);
x_5 = x_12;
x_6 = x_19;
goto block_11;
}
case 6:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
x_5 = x_12;
x_6 = x_20;
goto block_11;
}
case 7:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_12, 2);
lean_inc(x_21);
x_5 = x_12;
x_6 = x_21;
goto block_11;
}
case 8:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
x_5 = x_12;
x_6 = x_22;
goto block_11;
}
case 9:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
x_5 = x_12;
x_6 = x_23;
goto block_11;
}
default: 
{
lean_inc(x_12);
x_5 = x_12;
x_6 = x_12;
goto block_11;
}
}
}
else
{
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go_spec__0(x_1, x_2, x_7, x_8, x_9, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___redArg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_3);
lean_inc(x_8);
x_10 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_8, x_2, x_9, x_3);
lean_inc(x_10);
lean_inc(x_3);
x_11 = l_Lean_IR_FnBody_beq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_box(7);
lean_inc(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_3);
lean_inc(x_16);
x_19 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S_go(x_16, x_2, x_18, x_3);
lean_inc(x_19);
lean_inc(x_3);
x_20 = l_Lean_IR_FnBody_beq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_box(7);
lean_inc(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_1);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_8, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_5);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_13; 
x_6 = lean_box(1);
x_13 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_nat_dec_eq(x_1, x_14);
lean_dec(x_14);
x_7 = x_15;
goto block_12;
}
else
{
x_7 = x_5;
goto block_12;
}
block_12:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_4, x_3, x_10);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
lean_inc(x_5);
x_21 = lean_apply_3(x_1, x_20, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_9, 1, x_22);
x_12 = x_9;
x_13 = x_23;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_5);
x_26 = lean_apply_3(x_1, x_25, x_5, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_27);
x_12 = x_29;
x_13 = x_28;
goto block_18;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_1);
lean_inc(x_5);
x_32 = lean_apply_3(x_1, x_31, x_5, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_9, 0, x_33);
x_12 = x_9;
x_13 = x_34;
goto block_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_5);
x_36 = lean_apply_3(x_1, x_35, x_5, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_12 = x_39;
x_13 = x_38;
goto block_18;
}
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_11, x_3, x_12);
x_3 = x_15;
x_4 = x_16;
x_6 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_7, x_4, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_23 = l_Lean_IR_LocalContext_addJP(x_20, x_16, x_17, x_18);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_22);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_19, x_24, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_18, x_4, x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_dec(x_35);
lean_ctor_set(x_3, 3, x_28);
lean_ctor_set(x_3, 2, x_34);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 0, x_3);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_3, 3, x_28);
lean_ctor_set(x_3, 2, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
lean_ctor_set(x_3, 3, x_28);
lean_ctor_set(x_3, 2, x_40);
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_51 = l_Lean_IR_LocalContext_addJP(x_48, x_44, x_45, x_46);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_50);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_47, x_52, x_5);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_46, x_4, x_55);
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
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_64, 0, x_44);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_56);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
case 10:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_71, x_1);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_3);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_ctor_get(x_3, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_80);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___lam__0), 5, 2);
lean_closure_set(x_81, 0, x_1);
lean_closure_set(x_81, 1, x_2);
x_82 = lean_array_size(x_70);
x_83 = 0;
x_84 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0(x_81, x_82, x_83, x_70, x_4, x_5);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_ctor_set(x_3, 3, x_86);
x_88 = lean_box(x_72);
lean_ctor_set(x_84, 1, x_88);
lean_ctor_set(x_84, 0, x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
lean_ctor_set(x_3, 3, x_90);
x_92 = lean_box(x_72);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
else
{
lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_3);
x_95 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___lam__0), 5, 2);
lean_closure_set(x_95, 0, x_1);
lean_closure_set(x_95, 1, x_2);
x_96 = lean_array_size(x_70);
x_97 = 0;
x_98 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0(x_95, x_96, x_97, x_70, x_4, x_5);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_102, 0, x_67);
lean_ctor_set(x_102, 1, x_68);
lean_ctor_set(x_102, 2, x_69);
lean_ctor_set(x_102, 3, x_99);
x_103 = lean_box(x_72);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
}
default: 
{
uint8_t x_106; 
x_106 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_box(1);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_3, 3);
lean_inc(x_147);
x_108 = x_147;
goto block_146;
}
case 1:
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_3, 3);
lean_inc(x_148);
x_108 = x_148;
goto block_146;
}
case 2:
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_3, 3);
lean_inc(x_149);
x_108 = x_149;
goto block_146;
}
case 3:
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_3, 2);
lean_inc(x_150);
x_108 = x_150;
goto block_146;
}
case 4:
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_3, 3);
lean_inc(x_151);
x_108 = x_151;
goto block_146;
}
case 5:
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_3, 5);
lean_inc(x_152);
x_108 = x_152;
goto block_146;
}
case 6:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_3, 2);
lean_inc(x_153);
x_108 = x_153;
goto block_146;
}
case 7:
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_108 = x_154;
goto block_146;
}
case 8:
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_3, 1);
lean_inc(x_155);
x_108 = x_155;
goto block_146;
}
case 9:
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
x_108 = x_156;
goto block_146;
}
default: 
{
lean_inc(x_3);
x_108 = x_3;
goto block_146;
}
}
block_146:
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_box(13);
lean_inc(x_3);
x_110 = l_Lean_IR_FnBody_setBody(x_3, x_109);
x_111 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(x_110, x_1);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_112 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_108, x_4, x_5);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = !lean_is_exclusive(x_113);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_113, 0);
x_119 = lean_ctor_get(x_113, 1);
lean_dec(x_119);
x_120 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_110);
if (x_120 == 0)
{
uint8_t x_121; 
lean_free_object(x_113);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_unbox(x_114);
lean_dec(x_114);
x_6 = x_116;
x_7 = x_118;
x_8 = x_110;
x_9 = x_121;
goto block_14;
}
else
{
lean_object* x_122; uint8_t x_123; 
lean_dec(x_114);
x_122 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_118, x_4, x_116);
lean_dec(x_4);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
x_126 = l_Lean_IR_FnBody_setBody(x_110, x_124);
lean_ctor_set(x_122, 1, x_107);
lean_ctor_set(x_122, 0, x_126);
lean_ctor_set(x_113, 1, x_125);
lean_ctor_set(x_113, 0, x_122);
return x_113;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_122);
x_129 = l_Lean_IR_FnBody_setBody(x_110, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_107);
lean_ctor_set(x_113, 1, x_128);
lean_ctor_set(x_113, 0, x_130);
return x_113;
}
}
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
lean_dec(x_113);
x_132 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_110);
if (x_132 == 0)
{
uint8_t x_133; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_unbox(x_114);
lean_dec(x_114);
x_6 = x_116;
x_7 = x_131;
x_8 = x_110;
x_9 = x_133;
goto block_14;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_114);
x_134 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_131, x_4, x_116);
lean_dec(x_4);
lean_dec(x_2);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = l_Lean_IR_FnBody_setBody(x_110, x_135);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_107);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_112, 1);
lean_inc(x_141);
lean_dec(x_112);
x_142 = lean_ctor_get(x_113, 0);
lean_inc(x_142);
lean_dec(x_113);
x_143 = lean_unbox(x_114);
lean_dec(x_114);
x_6 = x_141;
x_7 = x_142;
x_8 = x_110;
x_9 = x_143;
goto block_14;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_3);
lean_ctor_set(x_144, 1, x_107);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_5);
return x_145;
}
}
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_2);
x_157 = lean_ctor_get(x_4, 0);
lean_inc(x_157);
lean_dec(x_4);
lean_inc(x_3);
x_158 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_157, x_1);
lean_dec(x_1);
x_159 = lean_box(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_3);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_5);
return x_161;
}
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_7);
x_11 = lean_box(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_7, x_4, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_nat_dec_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_nat_dec_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg(x_18, x_19, x_3);
lean_dec(x_18);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_4 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0;
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1;
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_box(0);
x_12 = lean_array_uset(x_5, x_4, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_6);
x_23 = l_Lean_IR_ResetReuse_R(x_22, x_6, x_7);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_21);
lean_ctor_set(x_10, 1, x_24);
x_35 = l_Lean_IR_CtorInfo_isScalar(x_21);
if (x_35 == 0)
{
x_26 = x_2;
goto block_34;
}
else
{
x_26 = x_35;
goto block_34;
}
block_34:
{
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_21);
lean_inc(x_1);
x_27 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(x_1, x_21, x_24, x_6, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_ctor_set(x_27, 1, x_29);
lean_ctor_set(x_27, 0, x_21);
x_13 = x_27;
x_14 = x_30;
goto block_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_31);
x_13 = x_33;
x_14 = x_32;
goto block_19;
}
}
else
{
lean_dec(x_24);
lean_dec(x_21);
x_13 = x_10;
x_14 = x_25;
goto block_19;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_49; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
lean_inc(x_6);
x_38 = l_Lean_IR_ResetReuse_R(x_37, x_6, x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
lean_inc(x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_39);
x_49 = l_Lean_IR_CtorInfo_isScalar(x_36);
if (x_49 == 0)
{
x_42 = x_2;
goto block_48;
}
else
{
x_42 = x_49;
goto block_48;
}
block_48:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_36);
lean_inc(x_1);
x_43 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(x_1, x_36, x_39, x_6, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_44);
x_13 = x_47;
x_14 = x_45;
goto block_19;
}
else
{
lean_dec(x_39);
lean_dec(x_36);
x_13 = x_41;
x_14 = x_40;
goto block_19;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_6);
x_52 = l_Lean_IR_ResetReuse_R(x_51, x_6, x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_ctor_set(x_10, 0, x_53);
x_13 = x_10;
x_14 = x_54;
goto block_19;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_10, 0);
lean_inc(x_55);
lean_dec(x_10);
lean_inc(x_6);
x_56 = l_Lean_IR_ResetReuse_R(x_55, x_6, x_7);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_13 = x_59;
x_14 = x_58;
goto block_19;
}
}
block_19:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_12, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_7 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_R(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_23 = l_Lean_IR_ResetReuse_R(x_21, x_2, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
x_28 = l_Lean_IR_LocalContext_addJP(x_27, x_19, x_20, x_24);
lean_ctor_set(x_2, 0, x_28);
x_29 = l_Lean_IR_ResetReuse_R(x_22, x_2, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_1, 3, x_31);
lean_ctor_set(x_1, 2, x_24);
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_1, 3, x_32);
lean_ctor_set(x_1, 2, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
x_38 = l_Lean_IR_LocalContext_addJP(x_35, x_19, x_20, x_24);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_37);
x_40 = l_Lean_IR_ResetReuse_R(x_22, x_39, x_25);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_24);
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ctor_get(x_1, 2);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
lean_inc(x_2);
x_49 = l_Lean_IR_ResetReuse_R(x_47, x_2, x_3);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_55 = x_2;
} else {
 lean_dec_ref(x_2);
 x_55 = lean_box(0);
}
lean_inc(x_50);
lean_inc(x_46);
lean_inc(x_45);
x_56 = l_Lean_IR_LocalContext_addJP(x_52, x_45, x_46, x_50);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 1);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_54);
x_58 = l_Lean_IR_ResetReuse_R(x_48, x_57, x_51);
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
x_62 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_46);
lean_ctor_set(x_62, 2, x_50);
lean_ctor_set(x_62, 3, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
case 10:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_66 = lean_ctor_get(x_1, 1);
x_67 = lean_ctor_get(x_1, 3);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(x_68, x_66);
x_70 = lean_box(0);
lean_inc(x_66);
x_71 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(x_68, x_66, x_70);
lean_ctor_set(x_2, 1, x_71);
x_72 = lean_array_size(x_67);
x_73 = 0;
lean_inc(x_66);
x_74 = l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(x_66, x_69, x_72, x_73, x_67, x_2, x_3);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_ctor_set(x_1, 3, x_76);
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
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_80 = lean_ctor_get(x_1, 1);
x_81 = lean_ctor_get(x_1, 3);
x_82 = lean_ctor_get(x_2, 0);
x_83 = lean_ctor_get(x_2, 1);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_2);
lean_inc(x_83);
x_85 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(x_83, x_80);
x_86 = lean_box(0);
lean_inc(x_80);
x_87 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(x_83, x_80, x_86);
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_84);
x_89 = lean_array_size(x_81);
x_90 = 0;
lean_inc(x_80);
x_91 = l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(x_80, x_85, x_89, x_90, x_81, x_88, x_3);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_92);
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_96 = lean_ctor_get(x_1, 0);
x_97 = lean_ctor_get(x_1, 1);
x_98 = lean_ctor_get(x_1, 2);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_1);
x_100 = lean_ctor_get(x_2, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_103 = x_2;
} else {
 lean_dec_ref(x_2);
 x_103 = lean_box(0);
}
lean_inc(x_101);
x_104 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(x_101, x_97);
x_105 = lean_box(0);
lean_inc(x_97);
x_106 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(x_101, x_97, x_105);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 2, 1);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_102);
x_108 = lean_array_size(x_99);
x_109 = 0;
lean_inc(x_97);
x_110 = l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(x_97, x_104, x_108, x_109, x_99, x_107, x_3);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_114, 0, x_96);
lean_ctor_set(x_114, 1, x_97);
lean_ctor_set(x_114, 2, x_98);
lean_ctor_set(x_114, 3, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
default: 
{
uint8_t x_116; 
x_116 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_116 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_1, 3);
lean_inc(x_117);
x_4 = x_117;
goto block_17;
}
case 1:
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_1, 3);
lean_inc(x_118);
x_4 = x_118;
goto block_17;
}
case 2:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_1, 3);
lean_inc(x_119);
x_4 = x_119;
goto block_17;
}
case 3:
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
x_4 = x_120;
goto block_17;
}
case 4:
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_1, 3);
lean_inc(x_121);
x_4 = x_121;
goto block_17;
}
case 5:
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_1, 5);
lean_inc(x_122);
x_4 = x_122;
goto block_17;
}
case 6:
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_1, 2);
lean_inc(x_123);
x_4 = x_123;
goto block_17;
}
case 7:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_1, 2);
lean_inc(x_124);
x_4 = x_124;
goto block_17;
}
case 8:
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
x_4 = x_125;
goto block_17;
}
case 9:
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
x_4 = x_126;
goto block_17;
}
default: 
{
lean_inc(x_1);
x_4 = x_1;
goto block_17;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_2);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_3);
return x_127;
}
}
}
block_17:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_IR_ResetReuse_R(x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(13);
x_9 = l_Lean_IR_FnBody_setBody(x_1, x_8);
x_10 = l_Lean_IR_FnBody_setBody(x_9, x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_box(13);
x_14 = l_Lean_IR_FnBody_setBody(x_1, x_13);
x_15 = l_Lean_IR_FnBody_setBody(x_14, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_ResetReuse_R_spec__4(x_1, x_8, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_ResetReuse_collectResets(x_15, x_5);
x_6 = x_16;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_IR_ResetReuse_collectResets(x_17, x_5);
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
block_12:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_5 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_collectResets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg(x_2, x_32, x_33);
x_1 = x_31;
x_2 = x_34;
goto _start;
}
else
{
lean_dec(x_30);
x_3 = x_1;
x_4 = x_2;
goto block_29;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_IR_ResetReuse_collectResets(x_36, x_2);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_1 = x_37;
x_2 = x_39;
goto _start;
}
case 10:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_size(x_41);
x_44 = lean_box(0);
x_45 = lean_nat_dec_lt(x_42, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_2);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_43, x_43);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_2);
return x_48;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0(x_41, x_49, x_50, x_44, x_2);
lean_dec(x_41);
return x_51;
}
}
}
default: 
{
x_3 = x_1;
x_4 = x_2;
goto block_29;
}
}
block_29:
{
uint8_t x_5; 
x_5 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_5 == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec(x_3);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
lean_dec(x_3);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
case 2:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_4;
goto _start;
}
case 3:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_1 = x_12;
x_2 = x_4;
goto _start;
}
case 4:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
lean_dec(x_3);
x_1 = x_14;
x_2 = x_4;
goto _start;
}
case 5:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
lean_dec(x_3);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
case 6:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec(x_3);
x_1 = x_18;
x_2 = x_4;
goto _start;
}
case 7:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_dec(x_3);
x_1 = x_20;
x_2 = x_4;
goto _start;
}
case 8:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_1 = x_22;
x_2 = x_4;
goto _start;
}
case 9:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_dec(x_3);
x_1 = x_24;
x_2 = x_4;
goto _start;
}
default: 
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ResetReuse_collectResets_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuseCore(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_IR_Decl_maxIndex(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0(lean_box(0));
x_7 = x_14;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0(lean_box(0));
lean_inc(x_3);
x_16 = l_Lean_IR_ResetReuse_collectResets(x_3, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_7 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_2);
x_10 = l_Lean_IR_ResetReuse_R(x_3, x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_Decl_updateBody_x21(x_1, x_11);
return x_12;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuseCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_IR_Decl_insertResetReuseCore(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_IR_Decl_insertResetReuseCore(x_1, x_3);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_IR_Decl_insertResetReuseCore(x_4, x_6);
return x_7;
}
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_LiveVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ResetReuse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LiveVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_ResetReuse_R_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__0);
l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at___Lean_IR_ResetReuse_R_spec__3___redArg___closed__1);
l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0 = _init_l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__0);
l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1 = _init_l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___Lean_IR_Decl_insertResetReuseCore_spec__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
