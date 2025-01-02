// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedProofs
// Imports: Init.Grind.Util Lean.Util.PtrSet Lean.Meta.Basic Lean.Meta.InferType
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap___rarg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1;
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__6___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_lt(x_4, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_instInhabitedExpr;
x_29 = l_outOfBounds___rarg(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_29, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_34 = lean_ptr_addr(x_31);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
x_36 = lean_array_set(x_24, x_4, x_31);
x_37 = 1;
x_38 = lean_box(x_37);
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_16 = x_39;
x_17 = x_32;
goto block_22;
}
else
{
lean_object* x_40; 
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_3);
x_16 = x_40;
x_17 = x_32;
goto block_22;
}
}
else
{
uint8_t x_41; 
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_fget(x_24, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_45);
x_46 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_45, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_50 = lean_ptr_addr(x_47);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_25);
x_52 = lean_array_set(x_24, x_4, x_47);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_3, 1, x_54);
lean_ctor_set(x_3, 0, x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_3);
x_16 = x_55;
x_17 = x_48;
goto block_22;
}
else
{
lean_object* x_56; 
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_3);
x_16 = x_56;
x_17 = x_48;
goto block_22;
}
}
else
{
uint8_t x_57; 
lean_dec(x_45);
lean_free_object(x_3);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_3, 0);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_3);
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_lt(x_4, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Lean_instInhabitedExpr;
x_66 = l_outOfBounds___rarg(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_66);
x_67 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_66, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_71 = lean_ptr_addr(x_68);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
x_73 = lean_array_set(x_61, x_4, x_68);
x_74 = 1;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_16 = x_77;
x_17 = x_69;
goto block_22;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_61);
lean_ctor_set(x_78, 1, x_62);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_16 = x_79;
x_17 = x_69;
goto block_22;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_80 = lean_ctor_get(x_67, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_82 = x_67;
} else {
 lean_dec_ref(x_67);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_array_fget(x_61, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_84);
x_85 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_84, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ptr_addr(x_84);
lean_dec(x_84);
x_89 = lean_ptr_addr(x_86);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_62);
x_91 = lean_array_set(x_61, x_4, x_86);
x_92 = 1;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_16 = x_95;
x_17 = x_87;
goto block_22;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_61);
lean_ctor_set(x_96, 1, x_62);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_16 = x_97;
x_17 = x_87;
goto block_22;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_100 = x_85;
} else {
 lean_dec_ref(x_85);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_20;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__6___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__6___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__5(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_1);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_5);
x_18 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_14, x_14, x_17, x_12, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_125; uint8_t x_126; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_125 = lean_ctor_get(x_19, 1);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_dec(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_21 = x_1;
goto block_124;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_19, 0);
lean_inc(x_127);
lean_dec(x_19);
x_128 = l_Lean_mkAppN(x_2, x_127);
lean_dec(x_127);
x_21 = x_128;
goto block_124;
}
block_124:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_st_ref_take(x_5, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_array_get_size(x_27);
x_29 = lean_ptr_addr(x_1);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_27, x_43);
x_45 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_46 = lean_nat_add(x_26, x_13);
lean_dec(x_26);
lean_inc(x_21);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_21);
lean_ctor_set(x_47, 2, x_44);
x_48 = lean_array_uset(x_27, x_43, x_47);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_nat_mul(x_46, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = lean_array_get_size(x_48);
x_54 = lean_nat_dec_le(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_48);
lean_ctor_set(x_23, 1, x_55);
lean_ctor_set(x_23, 0, x_46);
x_56 = lean_st_ref_set(x_5, x_23, x_24);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_21);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_21);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_ctor_set(x_23, 1, x_48);
lean_ctor_set(x_23, 0, x_46);
x_61 = lean_st_ref_set(x_5, x_23, x_24);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_21);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_box(0);
x_67 = lean_array_uset(x_27, x_43, x_66);
lean_inc(x_21);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_21, x_44);
x_69 = lean_array_uset(x_67, x_43, x_68);
lean_ctor_set(x_23, 1, x_69);
x_70 = lean_st_ref_set(x_5, x_23, x_24);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_21);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; lean_object* x_93; uint8_t x_94; 
x_75 = lean_ctor_get(x_23, 0);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_23);
x_77 = lean_array_get_size(x_76);
x_78 = lean_ptr_addr(x_1);
x_79 = lean_usize_to_uint64(x_78);
x_80 = 11;
x_81 = lean_uint64_mix_hash(x_79, x_80);
x_82 = 32;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = 16;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_90 = 1;
x_91 = lean_usize_sub(x_89, x_90);
x_92 = lean_usize_land(x_88, x_91);
x_93 = lean_array_uget(x_76, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_nat_add(x_75, x_13);
lean_dec(x_75);
lean_inc(x_21);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_21);
lean_ctor_set(x_96, 2, x_93);
x_97 = lean_array_uset(x_76, x_92, x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_mul(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_st_ref_set(x_5, x_105, x_24);
lean_dec(x_5);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_21);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_97);
x_111 = lean_st_ref_set(x_5, x_110, x_24);
lean_dec(x_5);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_21);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_box(0);
x_116 = lean_array_uset(x_76, x_92, x_115);
lean_inc(x_21);
x_117 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_21, x_93);
x_118 = lean_array_uset(x_116, x_92, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_75);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_st_ref_set(x_5, x_119, x_24);
lean_dec(x_5);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_21);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_18);
if (x_129 == 0)
{
return x_18;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_18, 0);
x_131 = lean_ctor_get(x_18, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_18);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 1:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_4);
x_133 = lean_array_get_size(x_3);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_135);
x_137 = 0;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_3);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_5);
x_140 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_136, x_136, x_139, x_134, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_247; uint8_t x_248; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_247 = lean_ctor_get(x_141, 1);
lean_inc(x_247);
x_248 = lean_unbox(x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_dec(x_141);
lean_dec(x_2);
lean_inc(x_1);
x_143 = x_1;
goto block_246;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_141, 0);
lean_inc(x_249);
lean_dec(x_141);
x_250 = l_Lean_mkAppN(x_2, x_249);
lean_dec(x_249);
x_143 = x_250;
goto block_246;
}
block_246:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_st_ref_take(x_5, x_142);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = !lean_is_exclusive(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; size_t x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; size_t x_161; size_t x_162; size_t x_163; size_t x_164; size_t x_165; lean_object* x_166; uint8_t x_167; 
x_148 = lean_ctor_get(x_145, 0);
x_149 = lean_ctor_get(x_145, 1);
x_150 = lean_array_get_size(x_149);
x_151 = lean_ptr_addr(x_1);
x_152 = lean_usize_to_uint64(x_151);
x_153 = 11;
x_154 = lean_uint64_mix_hash(x_152, x_153);
x_155 = 32;
x_156 = lean_uint64_shift_right(x_154, x_155);
x_157 = lean_uint64_xor(x_154, x_156);
x_158 = 16;
x_159 = lean_uint64_shift_right(x_157, x_158);
x_160 = lean_uint64_xor(x_157, x_159);
x_161 = lean_uint64_to_usize(x_160);
x_162 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_163 = 1;
x_164 = lean_usize_sub(x_162, x_163);
x_165 = lean_usize_land(x_161, x_164);
x_166 = lean_array_uget(x_149, x_165);
x_167 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_168 = lean_nat_add(x_148, x_135);
lean_dec(x_148);
lean_inc(x_143);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_143);
lean_ctor_set(x_169, 2, x_166);
x_170 = lean_array_uset(x_149, x_165, x_169);
x_171 = lean_unsigned_to_nat(4u);
x_172 = lean_nat_mul(x_168, x_171);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_div(x_172, x_173);
lean_dec(x_172);
x_175 = lean_array_get_size(x_170);
x_176 = lean_nat_dec_le(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_170);
lean_ctor_set(x_145, 1, x_177);
lean_ctor_set(x_145, 0, x_168);
x_178 = lean_st_ref_set(x_5, x_145, x_146);
lean_dec(x_5);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_178, 0);
lean_dec(x_180);
lean_ctor_set(x_178, 0, x_143);
return x_178;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_143);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_object* x_183; uint8_t x_184; 
lean_ctor_set(x_145, 1, x_170);
lean_ctor_set(x_145, 0, x_168);
x_183 = lean_st_ref_set(x_5, x_145, x_146);
lean_dec(x_5);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_183, 0);
lean_dec(x_185);
lean_ctor_set(x_183, 0, x_143);
return x_183;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_143);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_188 = lean_box(0);
x_189 = lean_array_uset(x_149, x_165, x_188);
lean_inc(x_143);
x_190 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_143, x_166);
x_191 = lean_array_uset(x_189, x_165, x_190);
lean_ctor_set(x_145, 1, x_191);
x_192 = lean_st_ref_set(x_5, x_145, x_146);
lean_dec(x_5);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
lean_ctor_set(x_192, 0, x_143);
return x_192;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_143);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; uint64_t x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; size_t x_210; size_t x_211; size_t x_212; size_t x_213; size_t x_214; lean_object* x_215; uint8_t x_216; 
x_197 = lean_ctor_get(x_145, 0);
x_198 = lean_ctor_get(x_145, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_145);
x_199 = lean_array_get_size(x_198);
x_200 = lean_ptr_addr(x_1);
x_201 = lean_usize_to_uint64(x_200);
x_202 = 11;
x_203 = lean_uint64_mix_hash(x_201, x_202);
x_204 = 32;
x_205 = lean_uint64_shift_right(x_203, x_204);
x_206 = lean_uint64_xor(x_203, x_205);
x_207 = 16;
x_208 = lean_uint64_shift_right(x_206, x_207);
x_209 = lean_uint64_xor(x_206, x_208);
x_210 = lean_uint64_to_usize(x_209);
x_211 = lean_usize_of_nat(x_199);
lean_dec(x_199);
x_212 = 1;
x_213 = lean_usize_sub(x_211, x_212);
x_214 = lean_usize_land(x_210, x_213);
x_215 = lean_array_uget(x_198, x_214);
x_216 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_217 = lean_nat_add(x_197, x_135);
lean_dec(x_197);
lean_inc(x_143);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_143);
lean_ctor_set(x_218, 2, x_215);
x_219 = lean_array_uset(x_198, x_214, x_218);
x_220 = lean_unsigned_to_nat(4u);
x_221 = lean_nat_mul(x_217, x_220);
x_222 = lean_unsigned_to_nat(3u);
x_223 = lean_nat_div(x_221, x_222);
lean_dec(x_221);
x_224 = lean_array_get_size(x_219);
x_225 = lean_nat_dec_le(x_223, x_224);
lean_dec(x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_219);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_st_ref_set(x_5, x_227, x_146);
lean_dec(x_5);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_143);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_217);
lean_ctor_set(x_232, 1, x_219);
x_233 = lean_st_ref_set(x_5, x_232, x_146);
lean_dec(x_5);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_143);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_box(0);
x_238 = lean_array_uset(x_198, x_214, x_237);
lean_inc(x_143);
x_239 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_143, x_215);
x_240 = lean_array_uset(x_238, x_214, x_239);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_197);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_st_ref_set(x_5, x_241, x_146);
lean_dec(x_5);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_143);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_140);
if (x_251 == 0)
{
return x_140;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_140, 0);
x_253 = lean_ctor_get(x_140, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_140);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
case 2:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_4);
x_255 = lean_array_get_size(x_3);
x_256 = lean_unsigned_to_nat(0u);
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_257);
x_259 = 0;
x_260 = lean_box(x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_3);
lean_ctor_set(x_261, 1, x_260);
lean_inc(x_5);
x_262 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_258, x_258, x_261, x_256, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_258);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_369; uint8_t x_370; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_369 = lean_ctor_get(x_263, 1);
lean_inc(x_369);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
lean_dec(x_263);
lean_dec(x_2);
lean_inc(x_1);
x_265 = x_1;
goto block_368;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_263, 0);
lean_inc(x_371);
lean_dec(x_263);
x_372 = l_Lean_mkAppN(x_2, x_371);
lean_dec(x_371);
x_265 = x_372;
goto block_368;
}
block_368:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_st_ref_take(x_5, x_264);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; size_t x_273; uint64_t x_274; uint64_t x_275; uint64_t x_276; uint64_t x_277; uint64_t x_278; uint64_t x_279; uint64_t x_280; uint64_t x_281; uint64_t x_282; size_t x_283; size_t x_284; size_t x_285; size_t x_286; size_t x_287; lean_object* x_288; uint8_t x_289; 
x_270 = lean_ctor_get(x_267, 0);
x_271 = lean_ctor_get(x_267, 1);
x_272 = lean_array_get_size(x_271);
x_273 = lean_ptr_addr(x_1);
x_274 = lean_usize_to_uint64(x_273);
x_275 = 11;
x_276 = lean_uint64_mix_hash(x_274, x_275);
x_277 = 32;
x_278 = lean_uint64_shift_right(x_276, x_277);
x_279 = lean_uint64_xor(x_276, x_278);
x_280 = 16;
x_281 = lean_uint64_shift_right(x_279, x_280);
x_282 = lean_uint64_xor(x_279, x_281);
x_283 = lean_uint64_to_usize(x_282);
x_284 = lean_usize_of_nat(x_272);
lean_dec(x_272);
x_285 = 1;
x_286 = lean_usize_sub(x_284, x_285);
x_287 = lean_usize_land(x_283, x_286);
x_288 = lean_array_uget(x_271, x_287);
x_289 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_290 = lean_nat_add(x_270, x_257);
lean_dec(x_270);
lean_inc(x_265);
x_291 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_291, 0, x_1);
lean_ctor_set(x_291, 1, x_265);
lean_ctor_set(x_291, 2, x_288);
x_292 = lean_array_uset(x_271, x_287, x_291);
x_293 = lean_unsigned_to_nat(4u);
x_294 = lean_nat_mul(x_290, x_293);
x_295 = lean_unsigned_to_nat(3u);
x_296 = lean_nat_div(x_294, x_295);
lean_dec(x_294);
x_297 = lean_array_get_size(x_292);
x_298 = lean_nat_dec_le(x_296, x_297);
lean_dec(x_297);
lean_dec(x_296);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_292);
lean_ctor_set(x_267, 1, x_299);
lean_ctor_set(x_267, 0, x_290);
x_300 = lean_st_ref_set(x_5, x_267, x_268);
lean_dec(x_5);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_300, 0);
lean_dec(x_302);
lean_ctor_set(x_300, 0, x_265);
return x_300;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_265);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
else
{
lean_object* x_305; uint8_t x_306; 
lean_ctor_set(x_267, 1, x_292);
lean_ctor_set(x_267, 0, x_290);
x_305 = lean_st_ref_set(x_5, x_267, x_268);
lean_dec(x_5);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_305, 0);
lean_dec(x_307);
lean_ctor_set(x_305, 0, x_265);
return x_305;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec(x_305);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_265);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_box(0);
x_311 = lean_array_uset(x_271, x_287, x_310);
lean_inc(x_265);
x_312 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_265, x_288);
x_313 = lean_array_uset(x_311, x_287, x_312);
lean_ctor_set(x_267, 1, x_313);
x_314 = lean_st_ref_set(x_5, x_267, x_268);
lean_dec(x_5);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_314, 0);
lean_dec(x_316);
lean_ctor_set(x_314, 0, x_265);
return x_314;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_265);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; size_t x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; uint64_t x_329; uint64_t x_330; uint64_t x_331; size_t x_332; size_t x_333; size_t x_334; size_t x_335; size_t x_336; lean_object* x_337; uint8_t x_338; 
x_319 = lean_ctor_get(x_267, 0);
x_320 = lean_ctor_get(x_267, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_267);
x_321 = lean_array_get_size(x_320);
x_322 = lean_ptr_addr(x_1);
x_323 = lean_usize_to_uint64(x_322);
x_324 = 11;
x_325 = lean_uint64_mix_hash(x_323, x_324);
x_326 = 32;
x_327 = lean_uint64_shift_right(x_325, x_326);
x_328 = lean_uint64_xor(x_325, x_327);
x_329 = 16;
x_330 = lean_uint64_shift_right(x_328, x_329);
x_331 = lean_uint64_xor(x_328, x_330);
x_332 = lean_uint64_to_usize(x_331);
x_333 = lean_usize_of_nat(x_321);
lean_dec(x_321);
x_334 = 1;
x_335 = lean_usize_sub(x_333, x_334);
x_336 = lean_usize_land(x_332, x_335);
x_337 = lean_array_uget(x_320, x_336);
x_338 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_339 = lean_nat_add(x_319, x_257);
lean_dec(x_319);
lean_inc(x_265);
x_340 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_340, 0, x_1);
lean_ctor_set(x_340, 1, x_265);
lean_ctor_set(x_340, 2, x_337);
x_341 = lean_array_uset(x_320, x_336, x_340);
x_342 = lean_unsigned_to_nat(4u);
x_343 = lean_nat_mul(x_339, x_342);
x_344 = lean_unsigned_to_nat(3u);
x_345 = lean_nat_div(x_343, x_344);
lean_dec(x_343);
x_346 = lean_array_get_size(x_341);
x_347 = lean_nat_dec_le(x_345, x_346);
lean_dec(x_346);
lean_dec(x_345);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_348 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_341);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_339);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_st_ref_set(x_5, x_349, x_268);
lean_dec(x_5);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_265);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_339);
lean_ctor_set(x_354, 1, x_341);
x_355 = lean_st_ref_set(x_5, x_354, x_268);
lean_dec(x_5);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_265);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_359 = lean_box(0);
x_360 = lean_array_uset(x_320, x_336, x_359);
lean_inc(x_265);
x_361 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_265, x_337);
x_362 = lean_array_uset(x_360, x_336, x_361);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_319);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_st_ref_set(x_5, x_363, x_268);
lean_dec(x_5);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_265);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_373 = !lean_is_exclusive(x_262);
if (x_373 == 0)
{
return x_262;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_262, 0);
x_375 = lean_ctor_get(x_262, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_262);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
case 3:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_4);
x_377 = lean_array_get_size(x_3);
x_378 = lean_unsigned_to_nat(0u);
x_379 = lean_unsigned_to_nat(1u);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_377);
lean_ctor_set(x_380, 2, x_379);
x_381 = 0;
x_382 = lean_box(x_381);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_3);
lean_ctor_set(x_383, 1, x_382);
lean_inc(x_5);
x_384 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_380, x_380, x_383, x_378, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_380);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_491; uint8_t x_492; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_491 = lean_ctor_get(x_385, 1);
lean_inc(x_491);
x_492 = lean_unbox(x_491);
lean_dec(x_491);
if (x_492 == 0)
{
lean_dec(x_385);
lean_dec(x_2);
lean_inc(x_1);
x_387 = x_1;
goto block_490;
}
else
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_385, 0);
lean_inc(x_493);
lean_dec(x_385);
x_494 = l_Lean_mkAppN(x_2, x_493);
lean_dec(x_493);
x_387 = x_494;
goto block_490;
}
block_490:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_388 = lean_st_ref_take(x_5, x_386);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = !lean_is_exclusive(x_389);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; size_t x_395; uint64_t x_396; uint64_t x_397; uint64_t x_398; uint64_t x_399; uint64_t x_400; uint64_t x_401; uint64_t x_402; uint64_t x_403; uint64_t x_404; size_t x_405; size_t x_406; size_t x_407; size_t x_408; size_t x_409; lean_object* x_410; uint8_t x_411; 
x_392 = lean_ctor_get(x_389, 0);
x_393 = lean_ctor_get(x_389, 1);
x_394 = lean_array_get_size(x_393);
x_395 = lean_ptr_addr(x_1);
x_396 = lean_usize_to_uint64(x_395);
x_397 = 11;
x_398 = lean_uint64_mix_hash(x_396, x_397);
x_399 = 32;
x_400 = lean_uint64_shift_right(x_398, x_399);
x_401 = lean_uint64_xor(x_398, x_400);
x_402 = 16;
x_403 = lean_uint64_shift_right(x_401, x_402);
x_404 = lean_uint64_xor(x_401, x_403);
x_405 = lean_uint64_to_usize(x_404);
x_406 = lean_usize_of_nat(x_394);
lean_dec(x_394);
x_407 = 1;
x_408 = lean_usize_sub(x_406, x_407);
x_409 = lean_usize_land(x_405, x_408);
x_410 = lean_array_uget(x_393, x_409);
x_411 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_412 = lean_nat_add(x_392, x_379);
lean_dec(x_392);
lean_inc(x_387);
x_413 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_413, 0, x_1);
lean_ctor_set(x_413, 1, x_387);
lean_ctor_set(x_413, 2, x_410);
x_414 = lean_array_uset(x_393, x_409, x_413);
x_415 = lean_unsigned_to_nat(4u);
x_416 = lean_nat_mul(x_412, x_415);
x_417 = lean_unsigned_to_nat(3u);
x_418 = lean_nat_div(x_416, x_417);
lean_dec(x_416);
x_419 = lean_array_get_size(x_414);
x_420 = lean_nat_dec_le(x_418, x_419);
lean_dec(x_419);
lean_dec(x_418);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_414);
lean_ctor_set(x_389, 1, x_421);
lean_ctor_set(x_389, 0, x_412);
x_422 = lean_st_ref_set(x_5, x_389, x_390);
lean_dec(x_5);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
lean_object* x_424; 
x_424 = lean_ctor_get(x_422, 0);
lean_dec(x_424);
lean_ctor_set(x_422, 0, x_387);
return x_422;
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_387);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
else
{
lean_object* x_427; uint8_t x_428; 
lean_ctor_set(x_389, 1, x_414);
lean_ctor_set(x_389, 0, x_412);
x_427 = lean_st_ref_set(x_5, x_389, x_390);
lean_dec(x_5);
x_428 = !lean_is_exclusive(x_427);
if (x_428 == 0)
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_427, 0);
lean_dec(x_429);
lean_ctor_set(x_427, 0, x_387);
return x_427;
}
else
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_387);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_432 = lean_box(0);
x_433 = lean_array_uset(x_393, x_409, x_432);
lean_inc(x_387);
x_434 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_387, x_410);
x_435 = lean_array_uset(x_433, x_409, x_434);
lean_ctor_set(x_389, 1, x_435);
x_436 = lean_st_ref_set(x_5, x_389, x_390);
lean_dec(x_5);
x_437 = !lean_is_exclusive(x_436);
if (x_437 == 0)
{
lean_object* x_438; 
x_438 = lean_ctor_get(x_436, 0);
lean_dec(x_438);
lean_ctor_set(x_436, 0, x_387);
return x_436;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_387);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; size_t x_444; uint64_t x_445; uint64_t x_446; uint64_t x_447; uint64_t x_448; uint64_t x_449; uint64_t x_450; uint64_t x_451; uint64_t x_452; uint64_t x_453; size_t x_454; size_t x_455; size_t x_456; size_t x_457; size_t x_458; lean_object* x_459; uint8_t x_460; 
x_441 = lean_ctor_get(x_389, 0);
x_442 = lean_ctor_get(x_389, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_389);
x_443 = lean_array_get_size(x_442);
x_444 = lean_ptr_addr(x_1);
x_445 = lean_usize_to_uint64(x_444);
x_446 = 11;
x_447 = lean_uint64_mix_hash(x_445, x_446);
x_448 = 32;
x_449 = lean_uint64_shift_right(x_447, x_448);
x_450 = lean_uint64_xor(x_447, x_449);
x_451 = 16;
x_452 = lean_uint64_shift_right(x_450, x_451);
x_453 = lean_uint64_xor(x_450, x_452);
x_454 = lean_uint64_to_usize(x_453);
x_455 = lean_usize_of_nat(x_443);
lean_dec(x_443);
x_456 = 1;
x_457 = lean_usize_sub(x_455, x_456);
x_458 = lean_usize_land(x_454, x_457);
x_459 = lean_array_uget(x_442, x_458);
x_460 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_461 = lean_nat_add(x_441, x_379);
lean_dec(x_441);
lean_inc(x_387);
x_462 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_462, 0, x_1);
lean_ctor_set(x_462, 1, x_387);
lean_ctor_set(x_462, 2, x_459);
x_463 = lean_array_uset(x_442, x_458, x_462);
x_464 = lean_unsigned_to_nat(4u);
x_465 = lean_nat_mul(x_461, x_464);
x_466 = lean_unsigned_to_nat(3u);
x_467 = lean_nat_div(x_465, x_466);
lean_dec(x_465);
x_468 = lean_array_get_size(x_463);
x_469 = lean_nat_dec_le(x_467, x_468);
lean_dec(x_468);
lean_dec(x_467);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_470 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_463);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_461);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_st_ref_set(x_5, x_471, x_390);
lean_dec(x_5);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_387);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_461);
lean_ctor_set(x_476, 1, x_463);
x_477 = lean_st_ref_set(x_5, x_476, x_390);
lean_dec(x_5);
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_479 = x_477;
} else {
 lean_dec_ref(x_477);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_387);
lean_ctor_set(x_480, 1, x_478);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_481 = lean_box(0);
x_482 = lean_array_uset(x_442, x_458, x_481);
lean_inc(x_387);
x_483 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_387, x_459);
x_484 = lean_array_uset(x_482, x_458, x_483);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_441);
lean_ctor_set(x_485, 1, x_484);
x_486 = lean_st_ref_set(x_5, x_485, x_390);
lean_dec(x_5);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_387);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_384);
if (x_495 == 0)
{
return x_384;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_384, 0);
x_497 = lean_ctor_get(x_384, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_384);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
case 4:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_4);
x_499 = lean_array_get_size(x_3);
x_500 = lean_unsigned_to_nat(0u);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_499);
lean_ctor_set(x_502, 2, x_501);
x_503 = 0;
x_504 = lean_box(x_503);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_3);
lean_ctor_set(x_505, 1, x_504);
lean_inc(x_5);
x_506 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_502, x_502, x_505, x_500, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_502);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_613; uint8_t x_614; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_613 = lean_ctor_get(x_507, 1);
lean_inc(x_613);
x_614 = lean_unbox(x_613);
lean_dec(x_613);
if (x_614 == 0)
{
lean_dec(x_507);
lean_dec(x_2);
lean_inc(x_1);
x_509 = x_1;
goto block_612;
}
else
{
lean_object* x_615; lean_object* x_616; 
x_615 = lean_ctor_get(x_507, 0);
lean_inc(x_615);
lean_dec(x_507);
x_616 = l_Lean_mkAppN(x_2, x_615);
lean_dec(x_615);
x_509 = x_616;
goto block_612;
}
block_612:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_510 = lean_st_ref_take(x_5, x_508);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = !lean_is_exclusive(x_511);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; size_t x_517; uint64_t x_518; uint64_t x_519; uint64_t x_520; uint64_t x_521; uint64_t x_522; uint64_t x_523; uint64_t x_524; uint64_t x_525; uint64_t x_526; size_t x_527; size_t x_528; size_t x_529; size_t x_530; size_t x_531; lean_object* x_532; uint8_t x_533; 
x_514 = lean_ctor_get(x_511, 0);
x_515 = lean_ctor_get(x_511, 1);
x_516 = lean_array_get_size(x_515);
x_517 = lean_ptr_addr(x_1);
x_518 = lean_usize_to_uint64(x_517);
x_519 = 11;
x_520 = lean_uint64_mix_hash(x_518, x_519);
x_521 = 32;
x_522 = lean_uint64_shift_right(x_520, x_521);
x_523 = lean_uint64_xor(x_520, x_522);
x_524 = 16;
x_525 = lean_uint64_shift_right(x_523, x_524);
x_526 = lean_uint64_xor(x_523, x_525);
x_527 = lean_uint64_to_usize(x_526);
x_528 = lean_usize_of_nat(x_516);
lean_dec(x_516);
x_529 = 1;
x_530 = lean_usize_sub(x_528, x_529);
x_531 = lean_usize_land(x_527, x_530);
x_532 = lean_array_uget(x_515, x_531);
x_533 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_534 = lean_nat_add(x_514, x_501);
lean_dec(x_514);
lean_inc(x_509);
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_1);
lean_ctor_set(x_535, 1, x_509);
lean_ctor_set(x_535, 2, x_532);
x_536 = lean_array_uset(x_515, x_531, x_535);
x_537 = lean_unsigned_to_nat(4u);
x_538 = lean_nat_mul(x_534, x_537);
x_539 = lean_unsigned_to_nat(3u);
x_540 = lean_nat_div(x_538, x_539);
lean_dec(x_538);
x_541 = lean_array_get_size(x_536);
x_542 = lean_nat_dec_le(x_540, x_541);
lean_dec(x_541);
lean_dec(x_540);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_543 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_536);
lean_ctor_set(x_511, 1, x_543);
lean_ctor_set(x_511, 0, x_534);
x_544 = lean_st_ref_set(x_5, x_511, x_512);
lean_dec(x_5);
x_545 = !lean_is_exclusive(x_544);
if (x_545 == 0)
{
lean_object* x_546; 
x_546 = lean_ctor_get(x_544, 0);
lean_dec(x_546);
lean_ctor_set(x_544, 0, x_509);
return x_544;
}
else
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
lean_dec(x_544);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_509);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
else
{
lean_object* x_549; uint8_t x_550; 
lean_ctor_set(x_511, 1, x_536);
lean_ctor_set(x_511, 0, x_534);
x_549 = lean_st_ref_set(x_5, x_511, x_512);
lean_dec(x_5);
x_550 = !lean_is_exclusive(x_549);
if (x_550 == 0)
{
lean_object* x_551; 
x_551 = lean_ctor_get(x_549, 0);
lean_dec(x_551);
lean_ctor_set(x_549, 0, x_509);
return x_549;
}
else
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
lean_dec(x_549);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_509);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_554 = lean_box(0);
x_555 = lean_array_uset(x_515, x_531, x_554);
lean_inc(x_509);
x_556 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_509, x_532);
x_557 = lean_array_uset(x_555, x_531, x_556);
lean_ctor_set(x_511, 1, x_557);
x_558 = lean_st_ref_set(x_5, x_511, x_512);
lean_dec(x_5);
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
lean_object* x_560; 
x_560 = lean_ctor_get(x_558, 0);
lean_dec(x_560);
lean_ctor_set(x_558, 0, x_509);
return x_558;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_509);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; size_t x_566; uint64_t x_567; uint64_t x_568; uint64_t x_569; uint64_t x_570; uint64_t x_571; uint64_t x_572; uint64_t x_573; uint64_t x_574; uint64_t x_575; size_t x_576; size_t x_577; size_t x_578; size_t x_579; size_t x_580; lean_object* x_581; uint8_t x_582; 
x_563 = lean_ctor_get(x_511, 0);
x_564 = lean_ctor_get(x_511, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_511);
x_565 = lean_array_get_size(x_564);
x_566 = lean_ptr_addr(x_1);
x_567 = lean_usize_to_uint64(x_566);
x_568 = 11;
x_569 = lean_uint64_mix_hash(x_567, x_568);
x_570 = 32;
x_571 = lean_uint64_shift_right(x_569, x_570);
x_572 = lean_uint64_xor(x_569, x_571);
x_573 = 16;
x_574 = lean_uint64_shift_right(x_572, x_573);
x_575 = lean_uint64_xor(x_572, x_574);
x_576 = lean_uint64_to_usize(x_575);
x_577 = lean_usize_of_nat(x_565);
lean_dec(x_565);
x_578 = 1;
x_579 = lean_usize_sub(x_577, x_578);
x_580 = lean_usize_land(x_576, x_579);
x_581 = lean_array_uget(x_564, x_580);
x_582 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_581);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_583 = lean_nat_add(x_563, x_501);
lean_dec(x_563);
lean_inc(x_509);
x_584 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_584, 0, x_1);
lean_ctor_set(x_584, 1, x_509);
lean_ctor_set(x_584, 2, x_581);
x_585 = lean_array_uset(x_564, x_580, x_584);
x_586 = lean_unsigned_to_nat(4u);
x_587 = lean_nat_mul(x_583, x_586);
x_588 = lean_unsigned_to_nat(3u);
x_589 = lean_nat_div(x_587, x_588);
lean_dec(x_587);
x_590 = lean_array_get_size(x_585);
x_591 = lean_nat_dec_le(x_589, x_590);
lean_dec(x_590);
lean_dec(x_589);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_592 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_585);
x_593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_593, 0, x_583);
lean_ctor_set(x_593, 1, x_592);
x_594 = lean_st_ref_set(x_5, x_593, x_512);
lean_dec(x_5);
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_509);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_583);
lean_ctor_set(x_598, 1, x_585);
x_599 = lean_st_ref_set(x_5, x_598, x_512);
lean_dec(x_5);
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_601 = x_599;
} else {
 lean_dec_ref(x_599);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_509);
lean_ctor_set(x_602, 1, x_600);
return x_602;
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_603 = lean_box(0);
x_604 = lean_array_uset(x_564, x_580, x_603);
lean_inc(x_509);
x_605 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_509, x_581);
x_606 = lean_array_uset(x_604, x_580, x_605);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_563);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_st_ref_set(x_5, x_607, x_512);
lean_dec(x_5);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_509);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_617 = !lean_is_exclusive(x_506);
if (x_617 == 0)
{
return x_506;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_506, 0);
x_619 = lean_ctor_get(x_506, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_506);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
case 5:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_621 = lean_ctor_get(x_2, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_2, 1);
lean_inc(x_622);
lean_dec(x_2);
x_623 = lean_array_set(x_3, x_4, x_622);
x_624 = lean_unsigned_to_nat(1u);
x_625 = lean_nat_sub(x_4, x_624);
lean_dec(x_4);
x_2 = x_621;
x_3 = x_623;
x_4 = x_625;
goto _start;
}
case 6:
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_4);
x_627 = lean_array_get_size(x_3);
x_628 = lean_unsigned_to_nat(0u);
x_629 = lean_unsigned_to_nat(1u);
x_630 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_627);
lean_ctor_set(x_630, 2, x_629);
x_631 = 0;
x_632 = lean_box(x_631);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_3);
lean_ctor_set(x_633, 1, x_632);
lean_inc(x_5);
x_634 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_630, x_630, x_633, x_628, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_630);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_741; uint8_t x_742; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_741 = lean_ctor_get(x_635, 1);
lean_inc(x_741);
x_742 = lean_unbox(x_741);
lean_dec(x_741);
if (x_742 == 0)
{
lean_dec(x_635);
lean_dec(x_2);
lean_inc(x_1);
x_637 = x_1;
goto block_740;
}
else
{
lean_object* x_743; lean_object* x_744; 
x_743 = lean_ctor_get(x_635, 0);
lean_inc(x_743);
lean_dec(x_635);
x_744 = l_Lean_mkAppN(x_2, x_743);
lean_dec(x_743);
x_637 = x_744;
goto block_740;
}
block_740:
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
x_638 = lean_st_ref_take(x_5, x_636);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = !lean_is_exclusive(x_639);
if (x_641 == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; size_t x_645; uint64_t x_646; uint64_t x_647; uint64_t x_648; uint64_t x_649; uint64_t x_650; uint64_t x_651; uint64_t x_652; uint64_t x_653; uint64_t x_654; size_t x_655; size_t x_656; size_t x_657; size_t x_658; size_t x_659; lean_object* x_660; uint8_t x_661; 
x_642 = lean_ctor_get(x_639, 0);
x_643 = lean_ctor_get(x_639, 1);
x_644 = lean_array_get_size(x_643);
x_645 = lean_ptr_addr(x_1);
x_646 = lean_usize_to_uint64(x_645);
x_647 = 11;
x_648 = lean_uint64_mix_hash(x_646, x_647);
x_649 = 32;
x_650 = lean_uint64_shift_right(x_648, x_649);
x_651 = lean_uint64_xor(x_648, x_650);
x_652 = 16;
x_653 = lean_uint64_shift_right(x_651, x_652);
x_654 = lean_uint64_xor(x_651, x_653);
x_655 = lean_uint64_to_usize(x_654);
x_656 = lean_usize_of_nat(x_644);
lean_dec(x_644);
x_657 = 1;
x_658 = lean_usize_sub(x_656, x_657);
x_659 = lean_usize_land(x_655, x_658);
x_660 = lean_array_uget(x_643, x_659);
x_661 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_660);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
x_662 = lean_nat_add(x_642, x_629);
lean_dec(x_642);
lean_inc(x_637);
x_663 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_663, 0, x_1);
lean_ctor_set(x_663, 1, x_637);
lean_ctor_set(x_663, 2, x_660);
x_664 = lean_array_uset(x_643, x_659, x_663);
x_665 = lean_unsigned_to_nat(4u);
x_666 = lean_nat_mul(x_662, x_665);
x_667 = lean_unsigned_to_nat(3u);
x_668 = lean_nat_div(x_666, x_667);
lean_dec(x_666);
x_669 = lean_array_get_size(x_664);
x_670 = lean_nat_dec_le(x_668, x_669);
lean_dec(x_669);
lean_dec(x_668);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_671 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_664);
lean_ctor_set(x_639, 1, x_671);
lean_ctor_set(x_639, 0, x_662);
x_672 = lean_st_ref_set(x_5, x_639, x_640);
lean_dec(x_5);
x_673 = !lean_is_exclusive(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
x_674 = lean_ctor_get(x_672, 0);
lean_dec(x_674);
lean_ctor_set(x_672, 0, x_637);
return x_672;
}
else
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 1);
lean_inc(x_675);
lean_dec(x_672);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_637);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
else
{
lean_object* x_677; uint8_t x_678; 
lean_ctor_set(x_639, 1, x_664);
lean_ctor_set(x_639, 0, x_662);
x_677 = lean_st_ref_set(x_5, x_639, x_640);
lean_dec(x_5);
x_678 = !lean_is_exclusive(x_677);
if (x_678 == 0)
{
lean_object* x_679; 
x_679 = lean_ctor_get(x_677, 0);
lean_dec(x_679);
lean_ctor_set(x_677, 0, x_637);
return x_677;
}
else
{
lean_object* x_680; lean_object* x_681; 
x_680 = lean_ctor_get(x_677, 1);
lean_inc(x_680);
lean_dec(x_677);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_637);
lean_ctor_set(x_681, 1, x_680);
return x_681;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
x_682 = lean_box(0);
x_683 = lean_array_uset(x_643, x_659, x_682);
lean_inc(x_637);
x_684 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_637, x_660);
x_685 = lean_array_uset(x_683, x_659, x_684);
lean_ctor_set(x_639, 1, x_685);
x_686 = lean_st_ref_set(x_5, x_639, x_640);
lean_dec(x_5);
x_687 = !lean_is_exclusive(x_686);
if (x_687 == 0)
{
lean_object* x_688; 
x_688 = lean_ctor_get(x_686, 0);
lean_dec(x_688);
lean_ctor_set(x_686, 0, x_637);
return x_686;
}
else
{
lean_object* x_689; lean_object* x_690; 
x_689 = lean_ctor_get(x_686, 1);
lean_inc(x_689);
lean_dec(x_686);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_637);
lean_ctor_set(x_690, 1, x_689);
return x_690;
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; size_t x_694; uint64_t x_695; uint64_t x_696; uint64_t x_697; uint64_t x_698; uint64_t x_699; uint64_t x_700; uint64_t x_701; uint64_t x_702; uint64_t x_703; size_t x_704; size_t x_705; size_t x_706; size_t x_707; size_t x_708; lean_object* x_709; uint8_t x_710; 
x_691 = lean_ctor_get(x_639, 0);
x_692 = lean_ctor_get(x_639, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_639);
x_693 = lean_array_get_size(x_692);
x_694 = lean_ptr_addr(x_1);
x_695 = lean_usize_to_uint64(x_694);
x_696 = 11;
x_697 = lean_uint64_mix_hash(x_695, x_696);
x_698 = 32;
x_699 = lean_uint64_shift_right(x_697, x_698);
x_700 = lean_uint64_xor(x_697, x_699);
x_701 = 16;
x_702 = lean_uint64_shift_right(x_700, x_701);
x_703 = lean_uint64_xor(x_700, x_702);
x_704 = lean_uint64_to_usize(x_703);
x_705 = lean_usize_of_nat(x_693);
lean_dec(x_693);
x_706 = 1;
x_707 = lean_usize_sub(x_705, x_706);
x_708 = lean_usize_land(x_704, x_707);
x_709 = lean_array_uget(x_692, x_708);
x_710 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_709);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; uint8_t x_719; 
x_711 = lean_nat_add(x_691, x_629);
lean_dec(x_691);
lean_inc(x_637);
x_712 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_712, 0, x_1);
lean_ctor_set(x_712, 1, x_637);
lean_ctor_set(x_712, 2, x_709);
x_713 = lean_array_uset(x_692, x_708, x_712);
x_714 = lean_unsigned_to_nat(4u);
x_715 = lean_nat_mul(x_711, x_714);
x_716 = lean_unsigned_to_nat(3u);
x_717 = lean_nat_div(x_715, x_716);
lean_dec(x_715);
x_718 = lean_array_get_size(x_713);
x_719 = lean_nat_dec_le(x_717, x_718);
lean_dec(x_718);
lean_dec(x_717);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_720 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_713);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_711);
lean_ctor_set(x_721, 1, x_720);
x_722 = lean_st_ref_set(x_5, x_721, x_640);
lean_dec(x_5);
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 x_724 = x_722;
} else {
 lean_dec_ref(x_722);
 x_724 = lean_box(0);
}
if (lean_is_scalar(x_724)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_724;
}
lean_ctor_set(x_725, 0, x_637);
lean_ctor_set(x_725, 1, x_723);
return x_725;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_726, 0, x_711);
lean_ctor_set(x_726, 1, x_713);
x_727 = lean_st_ref_set(x_5, x_726, x_640);
lean_dec(x_5);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_637);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_731 = lean_box(0);
x_732 = lean_array_uset(x_692, x_708, x_731);
lean_inc(x_637);
x_733 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_637, x_709);
x_734 = lean_array_uset(x_732, x_708, x_733);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_691);
lean_ctor_set(x_735, 1, x_734);
x_736 = lean_st_ref_set(x_5, x_735, x_640);
lean_dec(x_5);
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_738 = x_736;
} else {
 lean_dec_ref(x_736);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_637);
lean_ctor_set(x_739, 1, x_737);
return x_739;
}
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_634);
if (x_745 == 0)
{
return x_634;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_634, 0);
x_747 = lean_ctor_get(x_634, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_634);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
case 7:
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_4);
x_749 = lean_array_get_size(x_3);
x_750 = lean_unsigned_to_nat(0u);
x_751 = lean_unsigned_to_nat(1u);
x_752 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_749);
lean_ctor_set(x_752, 2, x_751);
x_753 = 0;
x_754 = lean_box(x_753);
x_755 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_755, 0, x_3);
lean_ctor_set(x_755, 1, x_754);
lean_inc(x_5);
x_756 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_752, x_752, x_755, x_750, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_752);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_863; uint8_t x_864; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec(x_756);
x_863 = lean_ctor_get(x_757, 1);
lean_inc(x_863);
x_864 = lean_unbox(x_863);
lean_dec(x_863);
if (x_864 == 0)
{
lean_dec(x_757);
lean_dec(x_2);
lean_inc(x_1);
x_759 = x_1;
goto block_862;
}
else
{
lean_object* x_865; lean_object* x_866; 
x_865 = lean_ctor_get(x_757, 0);
lean_inc(x_865);
lean_dec(x_757);
x_866 = l_Lean_mkAppN(x_2, x_865);
lean_dec(x_865);
x_759 = x_866;
goto block_862;
}
block_862:
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
x_760 = lean_st_ref_take(x_5, x_758);
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_760, 1);
lean_inc(x_762);
lean_dec(x_760);
x_763 = !lean_is_exclusive(x_761);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; size_t x_767; uint64_t x_768; uint64_t x_769; uint64_t x_770; uint64_t x_771; uint64_t x_772; uint64_t x_773; uint64_t x_774; uint64_t x_775; uint64_t x_776; size_t x_777; size_t x_778; size_t x_779; size_t x_780; size_t x_781; lean_object* x_782; uint8_t x_783; 
x_764 = lean_ctor_get(x_761, 0);
x_765 = lean_ctor_get(x_761, 1);
x_766 = lean_array_get_size(x_765);
x_767 = lean_ptr_addr(x_1);
x_768 = lean_usize_to_uint64(x_767);
x_769 = 11;
x_770 = lean_uint64_mix_hash(x_768, x_769);
x_771 = 32;
x_772 = lean_uint64_shift_right(x_770, x_771);
x_773 = lean_uint64_xor(x_770, x_772);
x_774 = 16;
x_775 = lean_uint64_shift_right(x_773, x_774);
x_776 = lean_uint64_xor(x_773, x_775);
x_777 = lean_uint64_to_usize(x_776);
x_778 = lean_usize_of_nat(x_766);
lean_dec(x_766);
x_779 = 1;
x_780 = lean_usize_sub(x_778, x_779);
x_781 = lean_usize_land(x_777, x_780);
x_782 = lean_array_uget(x_765, x_781);
x_783 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_782);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; uint8_t x_792; 
x_784 = lean_nat_add(x_764, x_751);
lean_dec(x_764);
lean_inc(x_759);
x_785 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_785, 0, x_1);
lean_ctor_set(x_785, 1, x_759);
lean_ctor_set(x_785, 2, x_782);
x_786 = lean_array_uset(x_765, x_781, x_785);
x_787 = lean_unsigned_to_nat(4u);
x_788 = lean_nat_mul(x_784, x_787);
x_789 = lean_unsigned_to_nat(3u);
x_790 = lean_nat_div(x_788, x_789);
lean_dec(x_788);
x_791 = lean_array_get_size(x_786);
x_792 = lean_nat_dec_le(x_790, x_791);
lean_dec(x_791);
lean_dec(x_790);
if (x_792 == 0)
{
lean_object* x_793; lean_object* x_794; uint8_t x_795; 
x_793 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_786);
lean_ctor_set(x_761, 1, x_793);
lean_ctor_set(x_761, 0, x_784);
x_794 = lean_st_ref_set(x_5, x_761, x_762);
lean_dec(x_5);
x_795 = !lean_is_exclusive(x_794);
if (x_795 == 0)
{
lean_object* x_796; 
x_796 = lean_ctor_get(x_794, 0);
lean_dec(x_796);
lean_ctor_set(x_794, 0, x_759);
return x_794;
}
else
{
lean_object* x_797; lean_object* x_798; 
x_797 = lean_ctor_get(x_794, 1);
lean_inc(x_797);
lean_dec(x_794);
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_759);
lean_ctor_set(x_798, 1, x_797);
return x_798;
}
}
else
{
lean_object* x_799; uint8_t x_800; 
lean_ctor_set(x_761, 1, x_786);
lean_ctor_set(x_761, 0, x_784);
x_799 = lean_st_ref_set(x_5, x_761, x_762);
lean_dec(x_5);
x_800 = !lean_is_exclusive(x_799);
if (x_800 == 0)
{
lean_object* x_801; 
x_801 = lean_ctor_get(x_799, 0);
lean_dec(x_801);
lean_ctor_set(x_799, 0, x_759);
return x_799;
}
else
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_799, 1);
lean_inc(x_802);
lean_dec(x_799);
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_759);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; 
x_804 = lean_box(0);
x_805 = lean_array_uset(x_765, x_781, x_804);
lean_inc(x_759);
x_806 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_759, x_782);
x_807 = lean_array_uset(x_805, x_781, x_806);
lean_ctor_set(x_761, 1, x_807);
x_808 = lean_st_ref_set(x_5, x_761, x_762);
lean_dec(x_5);
x_809 = !lean_is_exclusive(x_808);
if (x_809 == 0)
{
lean_object* x_810; 
x_810 = lean_ctor_get(x_808, 0);
lean_dec(x_810);
lean_ctor_set(x_808, 0, x_759);
return x_808;
}
else
{
lean_object* x_811; lean_object* x_812; 
x_811 = lean_ctor_get(x_808, 1);
lean_inc(x_811);
lean_dec(x_808);
x_812 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_812, 0, x_759);
lean_ctor_set(x_812, 1, x_811);
return x_812;
}
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; size_t x_816; uint64_t x_817; uint64_t x_818; uint64_t x_819; uint64_t x_820; uint64_t x_821; uint64_t x_822; uint64_t x_823; uint64_t x_824; uint64_t x_825; size_t x_826; size_t x_827; size_t x_828; size_t x_829; size_t x_830; lean_object* x_831; uint8_t x_832; 
x_813 = lean_ctor_get(x_761, 0);
x_814 = lean_ctor_get(x_761, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_761);
x_815 = lean_array_get_size(x_814);
x_816 = lean_ptr_addr(x_1);
x_817 = lean_usize_to_uint64(x_816);
x_818 = 11;
x_819 = lean_uint64_mix_hash(x_817, x_818);
x_820 = 32;
x_821 = lean_uint64_shift_right(x_819, x_820);
x_822 = lean_uint64_xor(x_819, x_821);
x_823 = 16;
x_824 = lean_uint64_shift_right(x_822, x_823);
x_825 = lean_uint64_xor(x_822, x_824);
x_826 = lean_uint64_to_usize(x_825);
x_827 = lean_usize_of_nat(x_815);
lean_dec(x_815);
x_828 = 1;
x_829 = lean_usize_sub(x_827, x_828);
x_830 = lean_usize_land(x_826, x_829);
x_831 = lean_array_uget(x_814, x_830);
x_832 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; uint8_t x_841; 
x_833 = lean_nat_add(x_813, x_751);
lean_dec(x_813);
lean_inc(x_759);
x_834 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_834, 0, x_1);
lean_ctor_set(x_834, 1, x_759);
lean_ctor_set(x_834, 2, x_831);
x_835 = lean_array_uset(x_814, x_830, x_834);
x_836 = lean_unsigned_to_nat(4u);
x_837 = lean_nat_mul(x_833, x_836);
x_838 = lean_unsigned_to_nat(3u);
x_839 = lean_nat_div(x_837, x_838);
lean_dec(x_837);
x_840 = lean_array_get_size(x_835);
x_841 = lean_nat_dec_le(x_839, x_840);
lean_dec(x_840);
lean_dec(x_839);
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_842 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_835);
x_843 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_843, 0, x_833);
lean_ctor_set(x_843, 1, x_842);
x_844 = lean_st_ref_set(x_5, x_843, x_762);
lean_dec(x_5);
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_846 = x_844;
} else {
 lean_dec_ref(x_844);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_759);
lean_ctor_set(x_847, 1, x_845);
return x_847;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_833);
lean_ctor_set(x_848, 1, x_835);
x_849 = lean_st_ref_set(x_5, x_848, x_762);
lean_dec(x_5);
x_850 = lean_ctor_get(x_849, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 x_851 = x_849;
} else {
 lean_dec_ref(x_849);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_759);
lean_ctor_set(x_852, 1, x_850);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_853 = lean_box(0);
x_854 = lean_array_uset(x_814, x_830, x_853);
lean_inc(x_759);
x_855 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_759, x_831);
x_856 = lean_array_uset(x_854, x_830, x_855);
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_813);
lean_ctor_set(x_857, 1, x_856);
x_858 = lean_st_ref_set(x_5, x_857, x_762);
lean_dec(x_5);
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_860 = x_858;
} else {
 lean_dec_ref(x_858);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_759);
lean_ctor_set(x_861, 1, x_859);
return x_861;
}
}
}
}
else
{
uint8_t x_867; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_867 = !lean_is_exclusive(x_756);
if (x_867 == 0)
{
return x_756;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_756, 0);
x_869 = lean_ctor_get(x_756, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_756);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
case 8:
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_4);
x_871 = lean_array_get_size(x_3);
x_872 = lean_unsigned_to_nat(0u);
x_873 = lean_unsigned_to_nat(1u);
x_874 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_871);
lean_ctor_set(x_874, 2, x_873);
x_875 = 0;
x_876 = lean_box(x_875);
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_3);
lean_ctor_set(x_877, 1, x_876);
lean_inc(x_5);
x_878 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_874, x_874, x_877, x_872, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_874);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_985; uint8_t x_986; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_985 = lean_ctor_get(x_879, 1);
lean_inc(x_985);
x_986 = lean_unbox(x_985);
lean_dec(x_985);
if (x_986 == 0)
{
lean_dec(x_879);
lean_dec(x_2);
lean_inc(x_1);
x_881 = x_1;
goto block_984;
}
else
{
lean_object* x_987; lean_object* x_988; 
x_987 = lean_ctor_get(x_879, 0);
lean_inc(x_987);
lean_dec(x_879);
x_988 = l_Lean_mkAppN(x_2, x_987);
lean_dec(x_987);
x_881 = x_988;
goto block_984;
}
block_984:
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
x_882 = lean_st_ref_take(x_5, x_880);
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
lean_dec(x_882);
x_885 = !lean_is_exclusive(x_883);
if (x_885 == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; size_t x_889; uint64_t x_890; uint64_t x_891; uint64_t x_892; uint64_t x_893; uint64_t x_894; uint64_t x_895; uint64_t x_896; uint64_t x_897; uint64_t x_898; size_t x_899; size_t x_900; size_t x_901; size_t x_902; size_t x_903; lean_object* x_904; uint8_t x_905; 
x_886 = lean_ctor_get(x_883, 0);
x_887 = lean_ctor_get(x_883, 1);
x_888 = lean_array_get_size(x_887);
x_889 = lean_ptr_addr(x_1);
x_890 = lean_usize_to_uint64(x_889);
x_891 = 11;
x_892 = lean_uint64_mix_hash(x_890, x_891);
x_893 = 32;
x_894 = lean_uint64_shift_right(x_892, x_893);
x_895 = lean_uint64_xor(x_892, x_894);
x_896 = 16;
x_897 = lean_uint64_shift_right(x_895, x_896);
x_898 = lean_uint64_xor(x_895, x_897);
x_899 = lean_uint64_to_usize(x_898);
x_900 = lean_usize_of_nat(x_888);
lean_dec(x_888);
x_901 = 1;
x_902 = lean_usize_sub(x_900, x_901);
x_903 = lean_usize_land(x_899, x_902);
x_904 = lean_array_uget(x_887, x_903);
x_905 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_904);
if (x_905 == 0)
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; uint8_t x_914; 
x_906 = lean_nat_add(x_886, x_873);
lean_dec(x_886);
lean_inc(x_881);
x_907 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_907, 0, x_1);
lean_ctor_set(x_907, 1, x_881);
lean_ctor_set(x_907, 2, x_904);
x_908 = lean_array_uset(x_887, x_903, x_907);
x_909 = lean_unsigned_to_nat(4u);
x_910 = lean_nat_mul(x_906, x_909);
x_911 = lean_unsigned_to_nat(3u);
x_912 = lean_nat_div(x_910, x_911);
lean_dec(x_910);
x_913 = lean_array_get_size(x_908);
x_914 = lean_nat_dec_le(x_912, x_913);
lean_dec(x_913);
lean_dec(x_912);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; uint8_t x_917; 
x_915 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_908);
lean_ctor_set(x_883, 1, x_915);
lean_ctor_set(x_883, 0, x_906);
x_916 = lean_st_ref_set(x_5, x_883, x_884);
lean_dec(x_5);
x_917 = !lean_is_exclusive(x_916);
if (x_917 == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_916, 0);
lean_dec(x_918);
lean_ctor_set(x_916, 0, x_881);
return x_916;
}
else
{
lean_object* x_919; lean_object* x_920; 
x_919 = lean_ctor_get(x_916, 1);
lean_inc(x_919);
lean_dec(x_916);
x_920 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_920, 0, x_881);
lean_ctor_set(x_920, 1, x_919);
return x_920;
}
}
else
{
lean_object* x_921; uint8_t x_922; 
lean_ctor_set(x_883, 1, x_908);
lean_ctor_set(x_883, 0, x_906);
x_921 = lean_st_ref_set(x_5, x_883, x_884);
lean_dec(x_5);
x_922 = !lean_is_exclusive(x_921);
if (x_922 == 0)
{
lean_object* x_923; 
x_923 = lean_ctor_get(x_921, 0);
lean_dec(x_923);
lean_ctor_set(x_921, 0, x_881);
return x_921;
}
else
{
lean_object* x_924; lean_object* x_925; 
x_924 = lean_ctor_get(x_921, 1);
lean_inc(x_924);
lean_dec(x_921);
x_925 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_925, 0, x_881);
lean_ctor_set(x_925, 1, x_924);
return x_925;
}
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; uint8_t x_931; 
x_926 = lean_box(0);
x_927 = lean_array_uset(x_887, x_903, x_926);
lean_inc(x_881);
x_928 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_881, x_904);
x_929 = lean_array_uset(x_927, x_903, x_928);
lean_ctor_set(x_883, 1, x_929);
x_930 = lean_st_ref_set(x_5, x_883, x_884);
lean_dec(x_5);
x_931 = !lean_is_exclusive(x_930);
if (x_931 == 0)
{
lean_object* x_932; 
x_932 = lean_ctor_get(x_930, 0);
lean_dec(x_932);
lean_ctor_set(x_930, 0, x_881);
return x_930;
}
else
{
lean_object* x_933; lean_object* x_934; 
x_933 = lean_ctor_get(x_930, 1);
lean_inc(x_933);
lean_dec(x_930);
x_934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_934, 0, x_881);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; size_t x_938; uint64_t x_939; uint64_t x_940; uint64_t x_941; uint64_t x_942; uint64_t x_943; uint64_t x_944; uint64_t x_945; uint64_t x_946; uint64_t x_947; size_t x_948; size_t x_949; size_t x_950; size_t x_951; size_t x_952; lean_object* x_953; uint8_t x_954; 
x_935 = lean_ctor_get(x_883, 0);
x_936 = lean_ctor_get(x_883, 1);
lean_inc(x_936);
lean_inc(x_935);
lean_dec(x_883);
x_937 = lean_array_get_size(x_936);
x_938 = lean_ptr_addr(x_1);
x_939 = lean_usize_to_uint64(x_938);
x_940 = 11;
x_941 = lean_uint64_mix_hash(x_939, x_940);
x_942 = 32;
x_943 = lean_uint64_shift_right(x_941, x_942);
x_944 = lean_uint64_xor(x_941, x_943);
x_945 = 16;
x_946 = lean_uint64_shift_right(x_944, x_945);
x_947 = lean_uint64_xor(x_944, x_946);
x_948 = lean_uint64_to_usize(x_947);
x_949 = lean_usize_of_nat(x_937);
lean_dec(x_937);
x_950 = 1;
x_951 = lean_usize_sub(x_949, x_950);
x_952 = lean_usize_land(x_948, x_951);
x_953 = lean_array_uget(x_936, x_952);
x_954 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_953);
if (x_954 == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; 
x_955 = lean_nat_add(x_935, x_873);
lean_dec(x_935);
lean_inc(x_881);
x_956 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_956, 0, x_1);
lean_ctor_set(x_956, 1, x_881);
lean_ctor_set(x_956, 2, x_953);
x_957 = lean_array_uset(x_936, x_952, x_956);
x_958 = lean_unsigned_to_nat(4u);
x_959 = lean_nat_mul(x_955, x_958);
x_960 = lean_unsigned_to_nat(3u);
x_961 = lean_nat_div(x_959, x_960);
lean_dec(x_959);
x_962 = lean_array_get_size(x_957);
x_963 = lean_nat_dec_le(x_961, x_962);
lean_dec(x_962);
lean_dec(x_961);
if (x_963 == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_964 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_957);
x_965 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_965, 0, x_955);
lean_ctor_set(x_965, 1, x_964);
x_966 = lean_st_ref_set(x_5, x_965, x_884);
lean_dec(x_5);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_968 = x_966;
} else {
 lean_dec_ref(x_966);
 x_968 = lean_box(0);
}
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(0, 2, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_881);
lean_ctor_set(x_969, 1, x_967);
return x_969;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_970 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_970, 0, x_955);
lean_ctor_set(x_970, 1, x_957);
x_971 = lean_st_ref_set(x_5, x_970, x_884);
lean_dec(x_5);
x_972 = lean_ctor_get(x_971, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_971)) {
 lean_ctor_release(x_971, 0);
 lean_ctor_release(x_971, 1);
 x_973 = x_971;
} else {
 lean_dec_ref(x_971);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(0, 2, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_881);
lean_ctor_set(x_974, 1, x_972);
return x_974;
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_975 = lean_box(0);
x_976 = lean_array_uset(x_936, x_952, x_975);
lean_inc(x_881);
x_977 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_881, x_953);
x_978 = lean_array_uset(x_976, x_952, x_977);
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_935);
lean_ctor_set(x_979, 1, x_978);
x_980 = lean_st_ref_set(x_5, x_979, x_884);
lean_dec(x_5);
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_982 = x_980;
} else {
 lean_dec_ref(x_980);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(0, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_881);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
}
}
}
else
{
uint8_t x_989; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_989 = !lean_is_exclusive(x_878);
if (x_989 == 0)
{
return x_878;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_878, 0);
x_991 = lean_ctor_get(x_878, 1);
lean_inc(x_991);
lean_inc(x_990);
lean_dec(x_878);
x_992 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
}
case 9:
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint8_t x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
lean_dec(x_4);
x_993 = lean_array_get_size(x_3);
x_994 = lean_unsigned_to_nat(0u);
x_995 = lean_unsigned_to_nat(1u);
x_996 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_996, 0, x_994);
lean_ctor_set(x_996, 1, x_993);
lean_ctor_set(x_996, 2, x_995);
x_997 = 0;
x_998 = lean_box(x_997);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_3);
lean_ctor_set(x_999, 1, x_998);
lean_inc(x_5);
x_1000 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_996, x_996, x_999, x_994, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_996);
if (lean_obj_tag(x_1000) == 0)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1107; uint8_t x_1108; 
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
lean_dec(x_1000);
x_1107 = lean_ctor_get(x_1001, 1);
lean_inc(x_1107);
x_1108 = lean_unbox(x_1107);
lean_dec(x_1107);
if (x_1108 == 0)
{
lean_dec(x_1001);
lean_dec(x_2);
lean_inc(x_1);
x_1003 = x_1;
goto block_1106;
}
else
{
lean_object* x_1109; lean_object* x_1110; 
x_1109 = lean_ctor_get(x_1001, 0);
lean_inc(x_1109);
lean_dec(x_1001);
x_1110 = l_Lean_mkAppN(x_2, x_1109);
lean_dec(x_1109);
x_1003 = x_1110;
goto block_1106;
}
block_1106:
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; 
x_1004 = lean_st_ref_take(x_5, x_1002);
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec(x_1004);
x_1007 = !lean_is_exclusive(x_1005);
if (x_1007 == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; size_t x_1011; uint64_t x_1012; uint64_t x_1013; uint64_t x_1014; uint64_t x_1015; uint64_t x_1016; uint64_t x_1017; uint64_t x_1018; uint64_t x_1019; uint64_t x_1020; size_t x_1021; size_t x_1022; size_t x_1023; size_t x_1024; size_t x_1025; lean_object* x_1026; uint8_t x_1027; 
x_1008 = lean_ctor_get(x_1005, 0);
x_1009 = lean_ctor_get(x_1005, 1);
x_1010 = lean_array_get_size(x_1009);
x_1011 = lean_ptr_addr(x_1);
x_1012 = lean_usize_to_uint64(x_1011);
x_1013 = 11;
x_1014 = lean_uint64_mix_hash(x_1012, x_1013);
x_1015 = 32;
x_1016 = lean_uint64_shift_right(x_1014, x_1015);
x_1017 = lean_uint64_xor(x_1014, x_1016);
x_1018 = 16;
x_1019 = lean_uint64_shift_right(x_1017, x_1018);
x_1020 = lean_uint64_xor(x_1017, x_1019);
x_1021 = lean_uint64_to_usize(x_1020);
x_1022 = lean_usize_of_nat(x_1010);
lean_dec(x_1010);
x_1023 = 1;
x_1024 = lean_usize_sub(x_1022, x_1023);
x_1025 = lean_usize_land(x_1021, x_1024);
x_1026 = lean_array_uget(x_1009, x_1025);
x_1027 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint8_t x_1036; 
x_1028 = lean_nat_add(x_1008, x_995);
lean_dec(x_1008);
lean_inc(x_1003);
x_1029 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1029, 0, x_1);
lean_ctor_set(x_1029, 1, x_1003);
lean_ctor_set(x_1029, 2, x_1026);
x_1030 = lean_array_uset(x_1009, x_1025, x_1029);
x_1031 = lean_unsigned_to_nat(4u);
x_1032 = lean_nat_mul(x_1028, x_1031);
x_1033 = lean_unsigned_to_nat(3u);
x_1034 = lean_nat_div(x_1032, x_1033);
lean_dec(x_1032);
x_1035 = lean_array_get_size(x_1030);
x_1036 = lean_nat_dec_le(x_1034, x_1035);
lean_dec(x_1035);
lean_dec(x_1034);
if (x_1036 == 0)
{
lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; 
x_1037 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1030);
lean_ctor_set(x_1005, 1, x_1037);
lean_ctor_set(x_1005, 0, x_1028);
x_1038 = lean_st_ref_set(x_5, x_1005, x_1006);
lean_dec(x_5);
x_1039 = !lean_is_exclusive(x_1038);
if (x_1039 == 0)
{
lean_object* x_1040; 
x_1040 = lean_ctor_get(x_1038, 0);
lean_dec(x_1040);
lean_ctor_set(x_1038, 0, x_1003);
return x_1038;
}
else
{
lean_object* x_1041; lean_object* x_1042; 
x_1041 = lean_ctor_get(x_1038, 1);
lean_inc(x_1041);
lean_dec(x_1038);
x_1042 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1042, 0, x_1003);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
else
{
lean_object* x_1043; uint8_t x_1044; 
lean_ctor_set(x_1005, 1, x_1030);
lean_ctor_set(x_1005, 0, x_1028);
x_1043 = lean_st_ref_set(x_5, x_1005, x_1006);
lean_dec(x_5);
x_1044 = !lean_is_exclusive(x_1043);
if (x_1044 == 0)
{
lean_object* x_1045; 
x_1045 = lean_ctor_get(x_1043, 0);
lean_dec(x_1045);
lean_ctor_set(x_1043, 0, x_1003);
return x_1043;
}
else
{
lean_object* x_1046; lean_object* x_1047; 
x_1046 = lean_ctor_get(x_1043, 1);
lean_inc(x_1046);
lean_dec(x_1043);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1003);
lean_ctor_set(x_1047, 1, x_1046);
return x_1047;
}
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; 
x_1048 = lean_box(0);
x_1049 = lean_array_uset(x_1009, x_1025, x_1048);
lean_inc(x_1003);
x_1050 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1003, x_1026);
x_1051 = lean_array_uset(x_1049, x_1025, x_1050);
lean_ctor_set(x_1005, 1, x_1051);
x_1052 = lean_st_ref_set(x_5, x_1005, x_1006);
lean_dec(x_5);
x_1053 = !lean_is_exclusive(x_1052);
if (x_1053 == 0)
{
lean_object* x_1054; 
x_1054 = lean_ctor_get(x_1052, 0);
lean_dec(x_1054);
lean_ctor_set(x_1052, 0, x_1003);
return x_1052;
}
else
{
lean_object* x_1055; lean_object* x_1056; 
x_1055 = lean_ctor_get(x_1052, 1);
lean_inc(x_1055);
lean_dec(x_1052);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1003);
lean_ctor_set(x_1056, 1, x_1055);
return x_1056;
}
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; size_t x_1060; uint64_t x_1061; uint64_t x_1062; uint64_t x_1063; uint64_t x_1064; uint64_t x_1065; uint64_t x_1066; uint64_t x_1067; uint64_t x_1068; uint64_t x_1069; size_t x_1070; size_t x_1071; size_t x_1072; size_t x_1073; size_t x_1074; lean_object* x_1075; uint8_t x_1076; 
x_1057 = lean_ctor_get(x_1005, 0);
x_1058 = lean_ctor_get(x_1005, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_1005);
x_1059 = lean_array_get_size(x_1058);
x_1060 = lean_ptr_addr(x_1);
x_1061 = lean_usize_to_uint64(x_1060);
x_1062 = 11;
x_1063 = lean_uint64_mix_hash(x_1061, x_1062);
x_1064 = 32;
x_1065 = lean_uint64_shift_right(x_1063, x_1064);
x_1066 = lean_uint64_xor(x_1063, x_1065);
x_1067 = 16;
x_1068 = lean_uint64_shift_right(x_1066, x_1067);
x_1069 = lean_uint64_xor(x_1066, x_1068);
x_1070 = lean_uint64_to_usize(x_1069);
x_1071 = lean_usize_of_nat(x_1059);
lean_dec(x_1059);
x_1072 = 1;
x_1073 = lean_usize_sub(x_1071, x_1072);
x_1074 = lean_usize_land(x_1070, x_1073);
x_1075 = lean_array_uget(x_1058, x_1074);
x_1076 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1075);
if (x_1076 == 0)
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; uint8_t x_1085; 
x_1077 = lean_nat_add(x_1057, x_995);
lean_dec(x_1057);
lean_inc(x_1003);
x_1078 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1078, 0, x_1);
lean_ctor_set(x_1078, 1, x_1003);
lean_ctor_set(x_1078, 2, x_1075);
x_1079 = lean_array_uset(x_1058, x_1074, x_1078);
x_1080 = lean_unsigned_to_nat(4u);
x_1081 = lean_nat_mul(x_1077, x_1080);
x_1082 = lean_unsigned_to_nat(3u);
x_1083 = lean_nat_div(x_1081, x_1082);
lean_dec(x_1081);
x_1084 = lean_array_get_size(x_1079);
x_1085 = lean_nat_dec_le(x_1083, x_1084);
lean_dec(x_1084);
lean_dec(x_1083);
if (x_1085 == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1086 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1079);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_1077);
lean_ctor_set(x_1087, 1, x_1086);
x_1088 = lean_st_ref_set(x_5, x_1087, x_1006);
lean_dec(x_5);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1090 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1091 = x_1090;
}
lean_ctor_set(x_1091, 0, x_1003);
lean_ctor_set(x_1091, 1, x_1089);
return x_1091;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1092 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1092, 0, x_1077);
lean_ctor_set(x_1092, 1, x_1079);
x_1093 = lean_st_ref_set(x_5, x_1092, x_1006);
lean_dec(x_5);
x_1094 = lean_ctor_get(x_1093, 1);
lean_inc(x_1094);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1095 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1095 = lean_box(0);
}
if (lean_is_scalar(x_1095)) {
 x_1096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1096 = x_1095;
}
lean_ctor_set(x_1096, 0, x_1003);
lean_ctor_set(x_1096, 1, x_1094);
return x_1096;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1097 = lean_box(0);
x_1098 = lean_array_uset(x_1058, x_1074, x_1097);
lean_inc(x_1003);
x_1099 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1003, x_1075);
x_1100 = lean_array_uset(x_1098, x_1074, x_1099);
x_1101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1101, 0, x_1057);
lean_ctor_set(x_1101, 1, x_1100);
x_1102 = lean_st_ref_set(x_5, x_1101, x_1006);
lean_dec(x_5);
x_1103 = lean_ctor_get(x_1102, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1102)) {
 lean_ctor_release(x_1102, 0);
 lean_ctor_release(x_1102, 1);
 x_1104 = x_1102;
} else {
 lean_dec_ref(x_1102);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1003);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
}
}
else
{
uint8_t x_1111; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1111 = !lean_is_exclusive(x_1000);
if (x_1111 == 0)
{
return x_1000;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1000, 0);
x_1113 = lean_ctor_get(x_1000, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1000);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
case 10:
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_4);
x_1115 = lean_array_get_size(x_3);
x_1116 = lean_unsigned_to_nat(0u);
x_1117 = lean_unsigned_to_nat(1u);
x_1118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1115);
lean_ctor_set(x_1118, 2, x_1117);
x_1119 = 0;
x_1120 = lean_box(x_1119);
x_1121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1121, 0, x_3);
lean_ctor_set(x_1121, 1, x_1120);
lean_inc(x_5);
x_1122 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_1118, x_1118, x_1121, x_1116, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1118);
if (lean_obj_tag(x_1122) == 0)
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1229; uint8_t x_1230; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
x_1229 = lean_ctor_get(x_1123, 1);
lean_inc(x_1229);
x_1230 = lean_unbox(x_1229);
lean_dec(x_1229);
if (x_1230 == 0)
{
lean_dec(x_1123);
lean_dec(x_2);
lean_inc(x_1);
x_1125 = x_1;
goto block_1228;
}
else
{
lean_object* x_1231; lean_object* x_1232; 
x_1231 = lean_ctor_get(x_1123, 0);
lean_inc(x_1231);
lean_dec(x_1123);
x_1232 = l_Lean_mkAppN(x_2, x_1231);
lean_dec(x_1231);
x_1125 = x_1232;
goto block_1228;
}
block_1228:
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; 
x_1126 = lean_st_ref_take(x_5, x_1124);
x_1127 = lean_ctor_get(x_1126, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1126, 1);
lean_inc(x_1128);
lean_dec(x_1126);
x_1129 = !lean_is_exclusive(x_1127);
if (x_1129 == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; size_t x_1133; uint64_t x_1134; uint64_t x_1135; uint64_t x_1136; uint64_t x_1137; uint64_t x_1138; uint64_t x_1139; uint64_t x_1140; uint64_t x_1141; uint64_t x_1142; size_t x_1143; size_t x_1144; size_t x_1145; size_t x_1146; size_t x_1147; lean_object* x_1148; uint8_t x_1149; 
x_1130 = lean_ctor_get(x_1127, 0);
x_1131 = lean_ctor_get(x_1127, 1);
x_1132 = lean_array_get_size(x_1131);
x_1133 = lean_ptr_addr(x_1);
x_1134 = lean_usize_to_uint64(x_1133);
x_1135 = 11;
x_1136 = lean_uint64_mix_hash(x_1134, x_1135);
x_1137 = 32;
x_1138 = lean_uint64_shift_right(x_1136, x_1137);
x_1139 = lean_uint64_xor(x_1136, x_1138);
x_1140 = 16;
x_1141 = lean_uint64_shift_right(x_1139, x_1140);
x_1142 = lean_uint64_xor(x_1139, x_1141);
x_1143 = lean_uint64_to_usize(x_1142);
x_1144 = lean_usize_of_nat(x_1132);
lean_dec(x_1132);
x_1145 = 1;
x_1146 = lean_usize_sub(x_1144, x_1145);
x_1147 = lean_usize_land(x_1143, x_1146);
x_1148 = lean_array_uget(x_1131, x_1147);
x_1149 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1148);
if (x_1149 == 0)
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; uint8_t x_1158; 
x_1150 = lean_nat_add(x_1130, x_1117);
lean_dec(x_1130);
lean_inc(x_1125);
x_1151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1151, 0, x_1);
lean_ctor_set(x_1151, 1, x_1125);
lean_ctor_set(x_1151, 2, x_1148);
x_1152 = lean_array_uset(x_1131, x_1147, x_1151);
x_1153 = lean_unsigned_to_nat(4u);
x_1154 = lean_nat_mul(x_1150, x_1153);
x_1155 = lean_unsigned_to_nat(3u);
x_1156 = lean_nat_div(x_1154, x_1155);
lean_dec(x_1154);
x_1157 = lean_array_get_size(x_1152);
x_1158 = lean_nat_dec_le(x_1156, x_1157);
lean_dec(x_1157);
lean_dec(x_1156);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; uint8_t x_1161; 
x_1159 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1152);
lean_ctor_set(x_1127, 1, x_1159);
lean_ctor_set(x_1127, 0, x_1150);
x_1160 = lean_st_ref_set(x_5, x_1127, x_1128);
lean_dec(x_5);
x_1161 = !lean_is_exclusive(x_1160);
if (x_1161 == 0)
{
lean_object* x_1162; 
x_1162 = lean_ctor_get(x_1160, 0);
lean_dec(x_1162);
lean_ctor_set(x_1160, 0, x_1125);
return x_1160;
}
else
{
lean_object* x_1163; lean_object* x_1164; 
x_1163 = lean_ctor_get(x_1160, 1);
lean_inc(x_1163);
lean_dec(x_1160);
x_1164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1164, 0, x_1125);
lean_ctor_set(x_1164, 1, x_1163);
return x_1164;
}
}
else
{
lean_object* x_1165; uint8_t x_1166; 
lean_ctor_set(x_1127, 1, x_1152);
lean_ctor_set(x_1127, 0, x_1150);
x_1165 = lean_st_ref_set(x_5, x_1127, x_1128);
lean_dec(x_5);
x_1166 = !lean_is_exclusive(x_1165);
if (x_1166 == 0)
{
lean_object* x_1167; 
x_1167 = lean_ctor_get(x_1165, 0);
lean_dec(x_1167);
lean_ctor_set(x_1165, 0, x_1125);
return x_1165;
}
else
{
lean_object* x_1168; lean_object* x_1169; 
x_1168 = lean_ctor_get(x_1165, 1);
lean_inc(x_1168);
lean_dec(x_1165);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_1125);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
x_1170 = lean_box(0);
x_1171 = lean_array_uset(x_1131, x_1147, x_1170);
lean_inc(x_1125);
x_1172 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1125, x_1148);
x_1173 = lean_array_uset(x_1171, x_1147, x_1172);
lean_ctor_set(x_1127, 1, x_1173);
x_1174 = lean_st_ref_set(x_5, x_1127, x_1128);
lean_dec(x_5);
x_1175 = !lean_is_exclusive(x_1174);
if (x_1175 == 0)
{
lean_object* x_1176; 
x_1176 = lean_ctor_get(x_1174, 0);
lean_dec(x_1176);
lean_ctor_set(x_1174, 0, x_1125);
return x_1174;
}
else
{
lean_object* x_1177; lean_object* x_1178; 
x_1177 = lean_ctor_get(x_1174, 1);
lean_inc(x_1177);
lean_dec(x_1174);
x_1178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1178, 0, x_1125);
lean_ctor_set(x_1178, 1, x_1177);
return x_1178;
}
}
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; size_t x_1182; uint64_t x_1183; uint64_t x_1184; uint64_t x_1185; uint64_t x_1186; uint64_t x_1187; uint64_t x_1188; uint64_t x_1189; uint64_t x_1190; uint64_t x_1191; size_t x_1192; size_t x_1193; size_t x_1194; size_t x_1195; size_t x_1196; lean_object* x_1197; uint8_t x_1198; 
x_1179 = lean_ctor_get(x_1127, 0);
x_1180 = lean_ctor_get(x_1127, 1);
lean_inc(x_1180);
lean_inc(x_1179);
lean_dec(x_1127);
x_1181 = lean_array_get_size(x_1180);
x_1182 = lean_ptr_addr(x_1);
x_1183 = lean_usize_to_uint64(x_1182);
x_1184 = 11;
x_1185 = lean_uint64_mix_hash(x_1183, x_1184);
x_1186 = 32;
x_1187 = lean_uint64_shift_right(x_1185, x_1186);
x_1188 = lean_uint64_xor(x_1185, x_1187);
x_1189 = 16;
x_1190 = lean_uint64_shift_right(x_1188, x_1189);
x_1191 = lean_uint64_xor(x_1188, x_1190);
x_1192 = lean_uint64_to_usize(x_1191);
x_1193 = lean_usize_of_nat(x_1181);
lean_dec(x_1181);
x_1194 = 1;
x_1195 = lean_usize_sub(x_1193, x_1194);
x_1196 = lean_usize_land(x_1192, x_1195);
x_1197 = lean_array_uget(x_1180, x_1196);
x_1198 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1197);
if (x_1198 == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; uint8_t x_1207; 
x_1199 = lean_nat_add(x_1179, x_1117);
lean_dec(x_1179);
lean_inc(x_1125);
x_1200 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1200, 0, x_1);
lean_ctor_set(x_1200, 1, x_1125);
lean_ctor_set(x_1200, 2, x_1197);
x_1201 = lean_array_uset(x_1180, x_1196, x_1200);
x_1202 = lean_unsigned_to_nat(4u);
x_1203 = lean_nat_mul(x_1199, x_1202);
x_1204 = lean_unsigned_to_nat(3u);
x_1205 = lean_nat_div(x_1203, x_1204);
lean_dec(x_1203);
x_1206 = lean_array_get_size(x_1201);
x_1207 = lean_nat_dec_le(x_1205, x_1206);
lean_dec(x_1206);
lean_dec(x_1205);
if (x_1207 == 0)
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1208 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1201);
x_1209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1209, 0, x_1199);
lean_ctor_set(x_1209, 1, x_1208);
x_1210 = lean_st_ref_set(x_5, x_1209, x_1128);
lean_dec(x_5);
x_1211 = lean_ctor_get(x_1210, 1);
lean_inc(x_1211);
if (lean_is_exclusive(x_1210)) {
 lean_ctor_release(x_1210, 0);
 lean_ctor_release(x_1210, 1);
 x_1212 = x_1210;
} else {
 lean_dec_ref(x_1210);
 x_1212 = lean_box(0);
}
if (lean_is_scalar(x_1212)) {
 x_1213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1213 = x_1212;
}
lean_ctor_set(x_1213, 0, x_1125);
lean_ctor_set(x_1213, 1, x_1211);
return x_1213;
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1214, 0, x_1199);
lean_ctor_set(x_1214, 1, x_1201);
x_1215 = lean_st_ref_set(x_5, x_1214, x_1128);
lean_dec(x_5);
x_1216 = lean_ctor_get(x_1215, 1);
lean_inc(x_1216);
if (lean_is_exclusive(x_1215)) {
 lean_ctor_release(x_1215, 0);
 lean_ctor_release(x_1215, 1);
 x_1217 = x_1215;
} else {
 lean_dec_ref(x_1215);
 x_1217 = lean_box(0);
}
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_1125);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1219 = lean_box(0);
x_1220 = lean_array_uset(x_1180, x_1196, x_1219);
lean_inc(x_1125);
x_1221 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1125, x_1197);
x_1222 = lean_array_uset(x_1220, x_1196, x_1221);
x_1223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1223, 0, x_1179);
lean_ctor_set(x_1223, 1, x_1222);
x_1224 = lean_st_ref_set(x_5, x_1223, x_1128);
lean_dec(x_5);
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
if (lean_is_exclusive(x_1224)) {
 lean_ctor_release(x_1224, 0);
 lean_ctor_release(x_1224, 1);
 x_1226 = x_1224;
} else {
 lean_dec_ref(x_1224);
 x_1226 = lean_box(0);
}
if (lean_is_scalar(x_1226)) {
 x_1227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1227 = x_1226;
}
lean_ctor_set(x_1227, 0, x_1125);
lean_ctor_set(x_1227, 1, x_1225);
return x_1227;
}
}
}
}
else
{
uint8_t x_1233; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1233 = !lean_is_exclusive(x_1122);
if (x_1233 == 0)
{
return x_1122;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1122, 0);
x_1235 = lean_ctor_get(x_1122, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1122);
x_1236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1236, 0, x_1234);
lean_ctor_set(x_1236, 1, x_1235);
return x_1236;
}
}
}
default: 
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; uint8_t x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_4);
x_1237 = lean_array_get_size(x_3);
x_1238 = lean_unsigned_to_nat(0u);
x_1239 = lean_unsigned_to_nat(1u);
x_1240 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1240, 0, x_1238);
lean_ctor_set(x_1240, 1, x_1237);
lean_ctor_set(x_1240, 2, x_1239);
x_1241 = 0;
x_1242 = lean_box(x_1241);
x_1243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1243, 0, x_3);
lean_ctor_set(x_1243, 1, x_1242);
lean_inc(x_5);
x_1244 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_1240, x_1240, x_1243, x_1238, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1240);
if (lean_obj_tag(x_1244) == 0)
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1351; uint8_t x_1352; 
x_1245 = lean_ctor_get(x_1244, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_1244, 1);
lean_inc(x_1246);
lean_dec(x_1244);
x_1351 = lean_ctor_get(x_1245, 1);
lean_inc(x_1351);
x_1352 = lean_unbox(x_1351);
lean_dec(x_1351);
if (x_1352 == 0)
{
lean_dec(x_1245);
lean_dec(x_2);
lean_inc(x_1);
x_1247 = x_1;
goto block_1350;
}
else
{
lean_object* x_1353; lean_object* x_1354; 
x_1353 = lean_ctor_get(x_1245, 0);
lean_inc(x_1353);
lean_dec(x_1245);
x_1354 = l_Lean_mkAppN(x_2, x_1353);
lean_dec(x_1353);
x_1247 = x_1354;
goto block_1350;
}
block_1350:
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; uint8_t x_1251; 
x_1248 = lean_st_ref_take(x_5, x_1246);
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1248, 1);
lean_inc(x_1250);
lean_dec(x_1248);
x_1251 = !lean_is_exclusive(x_1249);
if (x_1251 == 0)
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; size_t x_1255; uint64_t x_1256; uint64_t x_1257; uint64_t x_1258; uint64_t x_1259; uint64_t x_1260; uint64_t x_1261; uint64_t x_1262; uint64_t x_1263; uint64_t x_1264; size_t x_1265; size_t x_1266; size_t x_1267; size_t x_1268; size_t x_1269; lean_object* x_1270; uint8_t x_1271; 
x_1252 = lean_ctor_get(x_1249, 0);
x_1253 = lean_ctor_get(x_1249, 1);
x_1254 = lean_array_get_size(x_1253);
x_1255 = lean_ptr_addr(x_1);
x_1256 = lean_usize_to_uint64(x_1255);
x_1257 = 11;
x_1258 = lean_uint64_mix_hash(x_1256, x_1257);
x_1259 = 32;
x_1260 = lean_uint64_shift_right(x_1258, x_1259);
x_1261 = lean_uint64_xor(x_1258, x_1260);
x_1262 = 16;
x_1263 = lean_uint64_shift_right(x_1261, x_1262);
x_1264 = lean_uint64_xor(x_1261, x_1263);
x_1265 = lean_uint64_to_usize(x_1264);
x_1266 = lean_usize_of_nat(x_1254);
lean_dec(x_1254);
x_1267 = 1;
x_1268 = lean_usize_sub(x_1266, x_1267);
x_1269 = lean_usize_land(x_1265, x_1268);
x_1270 = lean_array_uget(x_1253, x_1269);
x_1271 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1270);
if (x_1271 == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; 
x_1272 = lean_nat_add(x_1252, x_1239);
lean_dec(x_1252);
lean_inc(x_1247);
x_1273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1273, 0, x_1);
lean_ctor_set(x_1273, 1, x_1247);
lean_ctor_set(x_1273, 2, x_1270);
x_1274 = lean_array_uset(x_1253, x_1269, x_1273);
x_1275 = lean_unsigned_to_nat(4u);
x_1276 = lean_nat_mul(x_1272, x_1275);
x_1277 = lean_unsigned_to_nat(3u);
x_1278 = lean_nat_div(x_1276, x_1277);
lean_dec(x_1276);
x_1279 = lean_array_get_size(x_1274);
x_1280 = lean_nat_dec_le(x_1278, x_1279);
lean_dec(x_1279);
lean_dec(x_1278);
if (x_1280 == 0)
{
lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; 
x_1281 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1274);
lean_ctor_set(x_1249, 1, x_1281);
lean_ctor_set(x_1249, 0, x_1272);
x_1282 = lean_st_ref_set(x_5, x_1249, x_1250);
lean_dec(x_5);
x_1283 = !lean_is_exclusive(x_1282);
if (x_1283 == 0)
{
lean_object* x_1284; 
x_1284 = lean_ctor_get(x_1282, 0);
lean_dec(x_1284);
lean_ctor_set(x_1282, 0, x_1247);
return x_1282;
}
else
{
lean_object* x_1285; lean_object* x_1286; 
x_1285 = lean_ctor_get(x_1282, 1);
lean_inc(x_1285);
lean_dec(x_1282);
x_1286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1286, 0, x_1247);
lean_ctor_set(x_1286, 1, x_1285);
return x_1286;
}
}
else
{
lean_object* x_1287; uint8_t x_1288; 
lean_ctor_set(x_1249, 1, x_1274);
lean_ctor_set(x_1249, 0, x_1272);
x_1287 = lean_st_ref_set(x_5, x_1249, x_1250);
lean_dec(x_5);
x_1288 = !lean_is_exclusive(x_1287);
if (x_1288 == 0)
{
lean_object* x_1289; 
x_1289 = lean_ctor_get(x_1287, 0);
lean_dec(x_1289);
lean_ctor_set(x_1287, 0, x_1247);
return x_1287;
}
else
{
lean_object* x_1290; lean_object* x_1291; 
x_1290 = lean_ctor_get(x_1287, 1);
lean_inc(x_1290);
lean_dec(x_1287);
x_1291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1291, 0, x_1247);
lean_ctor_set(x_1291, 1, x_1290);
return x_1291;
}
}
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; uint8_t x_1297; 
x_1292 = lean_box(0);
x_1293 = lean_array_uset(x_1253, x_1269, x_1292);
lean_inc(x_1247);
x_1294 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1247, x_1270);
x_1295 = lean_array_uset(x_1293, x_1269, x_1294);
lean_ctor_set(x_1249, 1, x_1295);
x_1296 = lean_st_ref_set(x_5, x_1249, x_1250);
lean_dec(x_5);
x_1297 = !lean_is_exclusive(x_1296);
if (x_1297 == 0)
{
lean_object* x_1298; 
x_1298 = lean_ctor_get(x_1296, 0);
lean_dec(x_1298);
lean_ctor_set(x_1296, 0, x_1247);
return x_1296;
}
else
{
lean_object* x_1299; lean_object* x_1300; 
x_1299 = lean_ctor_get(x_1296, 1);
lean_inc(x_1299);
lean_dec(x_1296);
x_1300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1300, 0, x_1247);
lean_ctor_set(x_1300, 1, x_1299);
return x_1300;
}
}
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; size_t x_1304; uint64_t x_1305; uint64_t x_1306; uint64_t x_1307; uint64_t x_1308; uint64_t x_1309; uint64_t x_1310; uint64_t x_1311; uint64_t x_1312; uint64_t x_1313; size_t x_1314; size_t x_1315; size_t x_1316; size_t x_1317; size_t x_1318; lean_object* x_1319; uint8_t x_1320; 
x_1301 = lean_ctor_get(x_1249, 0);
x_1302 = lean_ctor_get(x_1249, 1);
lean_inc(x_1302);
lean_inc(x_1301);
lean_dec(x_1249);
x_1303 = lean_array_get_size(x_1302);
x_1304 = lean_ptr_addr(x_1);
x_1305 = lean_usize_to_uint64(x_1304);
x_1306 = 11;
x_1307 = lean_uint64_mix_hash(x_1305, x_1306);
x_1308 = 32;
x_1309 = lean_uint64_shift_right(x_1307, x_1308);
x_1310 = lean_uint64_xor(x_1307, x_1309);
x_1311 = 16;
x_1312 = lean_uint64_shift_right(x_1310, x_1311);
x_1313 = lean_uint64_xor(x_1310, x_1312);
x_1314 = lean_uint64_to_usize(x_1313);
x_1315 = lean_usize_of_nat(x_1303);
lean_dec(x_1303);
x_1316 = 1;
x_1317 = lean_usize_sub(x_1315, x_1316);
x_1318 = lean_usize_land(x_1314, x_1317);
x_1319 = lean_array_uget(x_1302, x_1318);
x_1320 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_1319);
if (x_1320 == 0)
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; 
x_1321 = lean_nat_add(x_1301, x_1239);
lean_dec(x_1301);
lean_inc(x_1247);
x_1322 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1322, 0, x_1);
lean_ctor_set(x_1322, 1, x_1247);
lean_ctor_set(x_1322, 2, x_1319);
x_1323 = lean_array_uset(x_1302, x_1318, x_1322);
x_1324 = lean_unsigned_to_nat(4u);
x_1325 = lean_nat_mul(x_1321, x_1324);
x_1326 = lean_unsigned_to_nat(3u);
x_1327 = lean_nat_div(x_1325, x_1326);
lean_dec(x_1325);
x_1328 = lean_array_get_size(x_1323);
x_1329 = lean_nat_dec_le(x_1327, x_1328);
lean_dec(x_1328);
lean_dec(x_1327);
if (x_1329 == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1330 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_1323);
x_1331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1331, 0, x_1321);
lean_ctor_set(x_1331, 1, x_1330);
x_1332 = lean_st_ref_set(x_5, x_1331, x_1250);
lean_dec(x_5);
x_1333 = lean_ctor_get(x_1332, 1);
lean_inc(x_1333);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 lean_ctor_release(x_1332, 1);
 x_1334 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1334 = lean_box(0);
}
if (lean_is_scalar(x_1334)) {
 x_1335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1335 = x_1334;
}
lean_ctor_set(x_1335, 0, x_1247);
lean_ctor_set(x_1335, 1, x_1333);
return x_1335;
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1336, 0, x_1321);
lean_ctor_set(x_1336, 1, x_1323);
x_1337 = lean_st_ref_set(x_5, x_1336, x_1250);
lean_dec(x_5);
x_1338 = lean_ctor_get(x_1337, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1337)) {
 lean_ctor_release(x_1337, 0);
 lean_ctor_release(x_1337, 1);
 x_1339 = x_1337;
} else {
 lean_dec_ref(x_1337);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_1247);
lean_ctor_set(x_1340, 1, x_1338);
return x_1340;
}
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
x_1341 = lean_box(0);
x_1342 = lean_array_uset(x_1302, x_1318, x_1341);
lean_inc(x_1247);
x_1343 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_1247, x_1319);
x_1344 = lean_array_uset(x_1342, x_1318, x_1343);
x_1345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1345, 0, x_1301);
lean_ctor_set(x_1345, 1, x_1344);
x_1346 = lean_st_ref_set(x_5, x_1345, x_1250);
lean_dec(x_5);
x_1347 = lean_ctor_get(x_1346, 1);
lean_inc(x_1347);
if (lean_is_exclusive(x_1346)) {
 lean_ctor_release(x_1346, 0);
 lean_ctor_release(x_1346, 1);
 x_1348 = x_1346;
} else {
 lean_dec_ref(x_1346);
 x_1348 = lean_box(0);
}
if (lean_is_scalar(x_1348)) {
 x_1349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1349 = x_1348;
}
lean_ctor_set(x_1349, 0, x_1247);
lean_ctor_set(x_1349, 1, x_1347);
return x_1349;
}
}
}
}
else
{
uint8_t x_1355; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1355 = !lean_is_exclusive(x_1244);
if (x_1355 == 0)
{
return x_1244;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1356 = lean_ctor_get(x_1244, 0);
x_1357 = lean_ctor_get(x_1244, 1);
lean_inc(x_1357);
lean_inc(x_1356);
lean_dec(x_1244);
x_1358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1358, 0, x_1356);
lean_ctor_set(x_1358, 1, x_1357);
return x_1358;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_9);
x_11 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_1);
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__9(x_1, x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2;
x_3 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5;
lean_inc(x_1);
x_13 = l_Lean_mkAppB(x_12, x_10, x_1);
x_14 = lean_st_ref_take(x_3, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_ptr_addr(x_1);
x_22 = lean_usize_to_uint64(x_21);
x_23 = 11;
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_19, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_18, x_38);
lean_dec(x_18);
lean_inc(x_13);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_13);
lean_ctor_set(x_40, 2, x_36);
x_41 = lean_array_uset(x_19, x_35, x_40);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_nat_mul(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_41);
lean_ctor_set(x_15, 1, x_48);
lean_ctor_set(x_15, 0, x_39);
x_49 = lean_st_ref_set(x_3, x_15, x_16);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_13);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_ctor_set(x_15, 1, x_41);
lean_ctor_set(x_15, 0, x_39);
x_54 = lean_st_ref_set(x_3, x_15, x_16);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_13);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_59 = lean_box(0);
x_60 = lean_array_uset(x_19, x_35, x_59);
lean_inc(x_13);
x_61 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_13, x_36);
x_62 = lean_array_uset(x_60, x_35, x_61);
lean_ctor_set(x_15, 1, x_62);
x_63 = lean_st_ref_set(x_3, x_15, x_16);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_13);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_68 = lean_ctor_get(x_15, 0);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_15);
x_70 = lean_array_get_size(x_69);
x_71 = lean_ptr_addr(x_1);
x_72 = lean_usize_to_uint64(x_71);
x_73 = 11;
x_74 = lean_uint64_mix_hash(x_72, x_73);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_69, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_68, x_88);
lean_dec(x_68);
lean_inc(x_13);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_13);
lean_ctor_set(x_90, 2, x_86);
x_91 = lean_array_uset(x_69, x_85, x_90);
x_92 = lean_unsigned_to_nat(4u);
x_93 = lean_nat_mul(x_89, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__4(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_st_ref_set(x_3, x_99, x_16);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_13);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_91);
x_105 = lean_st_ref_set(x_3, x_104, x_16);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_13);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_box(0);
x_110 = lean_array_uset(x_69, x_85, x_109);
lean_inc(x_13);
x_111 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__8(x_1, x_13, x_86);
x_112 = lean_array_uset(x_110, x_85, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_68);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_st_ref_set(x_3, x_113, x_16);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_13);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_9);
if (x_118 == 0)
{
return x_9;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_9, 0);
x_120 = lean_ctor_get(x_9, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_9);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_13);
x_15 = lean_ptr_addr(x_1);
x_16 = lean_usize_to_uint64(x_15);
x_17 = 11;
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_13, x_29);
lean_dec(x_13);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(x_1, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_9);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_12);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_get_size(x_37);
x_39 = lean_ptr_addr(x_1);
x_40 = lean_usize_to_uint64(x_39);
x_41 = 11;
x_42 = lean_uint64_mix_hash(x_40, x_41);
x_43 = 32;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = 16;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = lean_uint64_to_usize(x_48);
x_50 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_51 = 1;
x_52 = lean_usize_sub(x_50, x_51);
x_53 = lean_usize_land(x_49, x_52);
x_54 = lean_array_uget(x_37, x_53);
lean_dec(x_37);
x_55 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(x_1, x_54);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_36);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_36);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.MarkNestedProofs", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.markNestedProofsImpl.visit", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1;
x_2 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2;
x_3 = lean_unsigned_to_nat(28u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_isProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4;
x_13 = l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_11);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_19);
x_21 = lean_ptr_addr(x_1);
x_22 = lean_usize_to_uint64(x_21);
x_23 = 11;
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = 32;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = 16;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_usize_land(x_31, x_34);
x_36 = lean_array_uget(x_19, x_35);
lean_dec(x_19);
x_37 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(x_1, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_15);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_18);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_15, 0, x_40);
return x_15;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_ptr_addr(x_1);
x_46 = lean_usize_to_uint64(x_45);
x_47 = 11;
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_43, x_59);
lean_dec(x_43);
x_61 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(x_1, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1(x_1, x_62, x_2, x_3, x_4, x_5, x_6, x_42);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_42);
return x_65;
}
}
}
case 10:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_dec(x_8);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_inc(x_68);
x_69 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_68, x_2, x_3, x_4, x_5, x_6, x_66);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; size_t x_72; size_t x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_73 = lean_ptr_addr(x_71);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_1);
x_75 = l_Lean_Expr_mdata___override(x_67, x_71);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
lean_dec(x_71);
lean_dec(x_67);
lean_ctor_set(x_69, 0, x_1);
return x_69;
}
}
else
{
lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_79 = lean_ptr_addr(x_76);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_1);
x_81 = l_Lean_Expr_mdata___override(x_67, x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_76);
lean_dec(x_67);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
return x_69;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 11:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_8, 1);
lean_inc(x_88);
lean_dec(x_8);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
lean_inc(x_91);
x_92 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_91, x_2, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; size_t x_95; size_t x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_96 = lean_ptr_addr(x_94);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_1);
x_98 = l_Lean_Expr_proj___override(x_89, x_90, x_94);
lean_ctor_set(x_92, 0, x_98);
return x_92;
}
else
{
lean_dec(x_94);
lean_dec(x_90);
lean_dec(x_89);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
}
else
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_92, 0);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_92);
x_101 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_102 = lean_ptr_addr(x_99);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_1);
x_104 = l_Lean_Expr_proj___override(x_89, x_90, x_99);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
else
{
lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_90);
lean_dec(x_89);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_100);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_92);
if (x_107 == 0)
{
return x_92;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_92, 0);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_92);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
default: 
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_8);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_8, 0);
lean_dec(x_112);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_8, 1);
lean_inc(x_113);
lean_dec(x_8);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_8);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_8, 1);
x_117 = lean_ctor_get(x_8, 0);
lean_dec(x_117);
x_118 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4;
x_119 = l_Lean_Expr_isAppOf(x_1, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_free_object(x_8);
x_120 = lean_box(0);
x_121 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3(x_1, x_120, x_2, x_3, x_4, x_5, x_6, x_116);
lean_dec(x_2);
return x_121;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_8, 1);
lean_inc(x_122);
lean_dec(x_8);
x_123 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4;
x_124 = l_Lean_Expr_isAppOf(x_1, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_box(0);
x_126 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3(x_1, x_125, x_2, x_3, x_4, x_5, x_6, x_122);
lean_dec(x_2);
return x_126;
}
else
{
lean_object* x_127; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_122);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_8);
if (x_128 == 0)
{
return x_8;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrMap___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl___closed__1;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__1);
l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_markNestedProofsImpl_visit___spec__1___closed__2);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__1___closed__1);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__1);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__2);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__3);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__4);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___lambda__2___closed__5);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4);
l_Lean_Meta_Grind_markNestedProofsImpl___closed__1 = _init_l_Lean_Meta_Grind_markNestedProofsImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
