// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.EmbeddedConstraint
// Imports: Std.Tactic.BVDecide.Normalize.Bool Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Meta.Tactic.Simp
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6;
extern lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6;
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Expr_hash(x_2);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(x_2, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_dec(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_14, x_34);
lean_dec(x_14);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_29);
x_38 = lean_array_uset(x_15, x_28, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_35, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_38);
lean_ctor_set(x_1, 1, x_45);
lean_ctor_set(x_1, 0, x_35);
lean_inc(x_9);
lean_inc(x_3);
x_46 = l_Lean_FVarId_getDecl(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_LocalDecl_toExpr(x_47);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_3);
x_51 = l_Lean_Meta_simpGlobalConfig;
x_52 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_50, x_49, x_51, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_1);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
return x_46;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_46, 0);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_46);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_35);
lean_inc(x_9);
lean_inc(x_3);
x_72 = l_Lean_FVarId_getDecl(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_LocalDecl_toExpr(x_73);
lean_dec(x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_3);
x_77 = l_Lean_Meta_simpGlobalConfig;
x_78 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_76, x_75, x_77, x_9, x_10, x_11, x_12, x_74);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_78, 0, x_83);
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_78, 0);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_1);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_5);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_1);
lean_dec(x_5);
x_90 = !lean_is_exclusive(x_78);
if (x_90 == 0)
{
return x_78;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_78, 0);
x_92 = lean_ctor_get(x_78, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_78);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_72);
if (x_94 == 0)
{
return x_72;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_72, 0);
x_96 = lean_ctor_get(x_72, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_72);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_1);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_14, x_98);
lean_dec(x_14);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_29);
x_102 = lean_array_uset(x_15, x_28, x_101);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_mul(x_99, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_102);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_9);
lean_inc(x_3);
x_111 = l_Lean_FVarId_getDecl(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_LocalDecl_toExpr(x_112);
lean_dec(x_112);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_3);
x_116 = l_Lean_Meta_simpGlobalConfig;
x_117 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_115, x_114, x_116, x_9, x_10, x_11, x_12, x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_110);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_120;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_110);
lean_dec(x_5);
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_110);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = lean_ctor_get(x_111, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_111, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_131 = x_111;
} else {
 lean_dec_ref(x_111);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_99);
lean_ctor_set(x_133, 1, x_102);
lean_inc(x_9);
lean_inc(x_3);
x_134 = l_Lean_FVarId_getDecl(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_LocalDecl_toExpr(x_135);
lean_dec(x_135);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_3);
x_139 = l_Lean_Meta_simpGlobalConfig;
x_140 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_138, x_137, x_139, x_9, x_10, x_11, x_12, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_133);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_5);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
lean_dec(x_5);
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_150 = x_140;
} else {
 lean_dec_ref(x_140);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_134, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_134, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_154 = x_134;
} else {
 lean_dec_ref(x_134);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_156 = lean_array_push(x_5, x_3);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_4);
lean_ctor_set(x_157, 1, x_1);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_13);
return x_160;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_cleanupAnnotations(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_3, x_1, x_4, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1(x_1, x_5, x_2, x_3, x_4, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_16 = lean_array_uget(x_3, x_5);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_16);
x_30 = l_Lean_FVarId_getType(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_cleanupAnnotations(x_31);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_16);
x_35 = lean_box(0);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_28, x_29, x_27, x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_17 = x_37;
x_18 = x_38;
goto block_25;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Expr_appArg(x_33, lean_box(0));
x_40 = l_Lean_Expr_appFnCleanup(x_33, lean_box(0));
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_16);
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_28, x_29, x_27, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_17 = x_44;
x_18 = x_45;
goto block_25;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Expr_appArg(x_40, lean_box(0));
x_47 = l_Lean_Expr_appFnCleanup(x_40, lean_box(0));
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_16);
x_49 = lean_box(0);
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_28, x_29, x_27, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_17 = x_51;
x_18 = x_52;
goto block_25;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l_Lean_Expr_appFnCleanup(x_47, lean_box(0));
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2;
x_55 = l_Lean_Expr_isConstOf(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_16);
x_56 = lean_box(0);
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_28, x_29, x_27, x_56, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_17 = x_58;
x_18 = x_59;
goto block_25;
}
else
{
lean_object* x_60; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_60 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3(x_29, x_16, x_28, x_27, x_46, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_17 = x_61;
x_18 = x_62;
goto block_25;
}
else
{
uint8_t x_63; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_67 = !lean_is_exclusive(x_30);
if (x_67 == 0)
{
return x_30;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
x_13 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getPropHyps(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2___rarg(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(2u);
x_21 = 0;
x_22 = 1;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 2, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 3, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 5, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 7, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 9, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 10, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 11, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 12, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 13, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 14, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 15, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 17, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 18, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 19, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 20, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 21, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 22, x_22);
x_25 = l_Lean_Meta_Simp_mkContext(x_24, x_3, x_17, x_8, x_9, x_10, x_11, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8;
x_30 = l_Lean_Meta_simpGoal(x_1, x_26, x_4, x_28, x_22, x_14, x_29, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_ctor_set(x_32, 0, x_41);
lean_ctor_set(x_30, 0, x_32);
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_32, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_48 = x_30;
} else {
 lean_dec_ref(x_30);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_30, 0);
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_array_size(x_3);
x_13 = 0;
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1(x_3, x_11, x_3, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_MVarId_tryClearMany(x_1, x_19, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Array_isEmpty___rarg(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_21);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1;
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2(x_23, x_2, x_20, x_26, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = l_Array_isEmpty___rarg(x_20);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1;
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2(x_30, x_2, x_20, x_33, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___boxed), 10, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__3___rarg), 9, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__2___rarg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("embeddedConstraintSubsitution", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___lambda__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___spec__1___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__2___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___lambda__3___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___elambda__1___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
