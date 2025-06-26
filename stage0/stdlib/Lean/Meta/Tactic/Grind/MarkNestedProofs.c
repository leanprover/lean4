// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedProofs
// Imports: Init.Grind.Util Lean.Util.PtrSet Lean.Meta.Transform Lean.Meta.Basic Lean.Meta.InferType Lean.Meta.Tactic.Grind.Util
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3;
static lean_object* l_Lean_Meta_Grind_markProof_unsafe__1___closed__0;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3;
lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2;
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0;
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Core_betaReduce(x_10, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_Grind_unfoldReducible(x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = lean_apply_7(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_Grind_eraseIrrelevantMData(x_19, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_Grind_foldProjs(x_22, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_normalizeLevels(x_25, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4;
x_31 = l_Lean_mkAppB(x_30, x_29, x_1);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4;
x_35 = l_Lean_mkAppB(x_34, x_32, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_dec(x_1);
return x_27;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_24;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_11);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_5, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_19 = lean_array_get(x_1, x_17, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_19, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_27; size_t x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_27 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_28 = lean_ptr_addr(x_21);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_30 = lean_array_set(x_17, x_5, x_21);
x_31 = lean_box(x_2);
lean_ctor_set(x_4, 1, x_31);
lean_ctor_set(x_4, 0, x_30);
x_23 = x_4;
goto block_26;
}
else
{
lean_dec(x_21);
x_23 = x_4;
goto block_26;
}
block_26:
{
lean_object* x_24; 
x_24 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_23;
x_5 = x_24;
x_11 = x_22;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_free_object(x_4);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_1);
x_38 = lean_array_get(x_1, x_36, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_38);
x_39 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_38, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_46; size_t x_47; uint8_t x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_46 = lean_ptr_addr(x_38);
lean_dec(x_38);
x_47 = lean_ptr_addr(x_40);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
x_49 = lean_array_set(x_36, x_5, x_40);
x_50 = lean_box(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_42 = x_51;
goto block_45;
}
else
{
lean_object* x_52; 
lean_dec(x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_37);
x_42 = x_52;
goto block_45;
}
block_45:
{
lean_object* x_43; 
x_43 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_42;
x_5 = x_43;
x_11 = x_41;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_array_set(x_6, x_7, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_5 = x_14;
x_6 = x_16;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_6);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_box(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_2, x_3, x_23, x_25, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
lean_ctor_set(x_26, 0, x_4);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l_Lean_mkAppN(x_5, x_36);
lean_dec(x_36);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
x_40 = l_Lean_mkAppN(x_5, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0;
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1;
x_20 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2;
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
x_38 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_inc(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
x_46 = l_Lean_instInhabitedExpr;
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, x_7);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
x_55 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_inc(x_50);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_62);
x_63 = l_ReaderT_instMonad___redArg(x_27);
x_64 = l_Lean_instInhabitedExpr;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, x_7);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
x_75 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_inc(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = l_Lean_instInhabitedExpr;
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, x_7);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1;
x_94 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2;
lean_inc(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
x_111 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_inc(x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_108);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_116, 0, x_107);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_117, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_115);
if (lean_is_scalar(x_104)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_104;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = l_ReaderT_instMonad___redArg(x_119);
x_121 = l_Lean_instInhabitedExpr;
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, x_7);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1;
x_132 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2;
lean_inc(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3;
x_150 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4;
lean_inc(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = l_Lean_instInhabitedExpr;
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, x_7);
return x_163;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_19; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_ptr_addr(x_1);
x_24 = lean_usize_to_uint64(x_23);
x_25 = 11;
x_26 = lean_uint64_mix_hash(x_24, x_25);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_21, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_20, x_40);
lean_dec(x_20);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_38);
x_43 = lean_array_uset(x_21, x_37, x_42);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_mul(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_43);
lean_ctor_set(x_10, 1, x_50);
lean_ctor_set(x_10, 0, x_41);
x_12 = x_10;
goto block_18;
}
else
{
lean_ctor_set(x_10, 1, x_43);
lean_ctor_set(x_10, 0, x_41);
x_12 = x_10;
goto block_18;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_box(0);
x_52 = lean_array_uset(x_21, x_37, x_51);
lean_inc(x_2);
x_53 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_38);
x_54 = lean_array_uset(x_52, x_37, x_53);
lean_ctor_set(x_10, 1, x_54);
x_12 = x_10;
goto block_18;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_55 = lean_ctor_get(x_10, 0);
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_10);
x_57 = lean_array_get_size(x_56);
x_58 = lean_ptr_addr(x_1);
x_59 = lean_usize_to_uint64(x_58);
x_60 = 11;
x_61 = lean_uint64_mix_hash(x_59, x_60);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_56, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_55, x_75);
lean_dec(x_55);
lean_inc(x_2);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_2);
lean_ctor_set(x_77, 2, x_73);
x_78 = lean_array_uset(x_56, x_72, x_77);
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_nat_mul(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_12 = x_86;
goto block_18;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_78);
x_12 = x_87;
goto block_18;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_box(0);
x_89 = lean_array_uset(x_56, x_72, x_88);
lean_inc(x_2);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_73);
x_91 = lean_array_uset(x_89, x_72, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_55);
lean_ctor_set(x_92, 1, x_91);
x_12 = x_92;
goto block_18;
}
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_set(x_3, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
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
x_1 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(78u);
x_4 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2;
x_5 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_50; uint8_t x_51; uint8_t x_198; uint8_t x_203; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_12 = x_8;
} else {
 lean_dec_ref(x_8);
 x_12 = lean_box(0);
}
x_50 = l_Lean_instInhabitedExpr;
x_203 = l_Lean_Expr_isApp(x_1);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_Lean_Expr_isForall(x_1);
x_198 = x_204;
goto block_202;
}
else
{
x_198 = x_203;
goto block_202;
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_forallE___override(x_21, x_19, x_20, x_18);
x_25 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_24, x_13, x_15, x_22, x_16, x_14, x_17);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_18, x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_forallE___override(x_21, x_19, x_20, x_18);
x_28 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_27, x_13, x_15, x_22, x_16, x_14, x_17);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_1);
x_29 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_13, x_15, x_22, x_16, x_14, x_17);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_13);
return x_29;
}
}
}
block_49:
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_44 = lean_ptr_addr(x_34);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_32);
x_13 = x_37;
x_14 = x_41;
x_15 = x_38;
x_16 = x_40;
x_17 = x_42;
x_18 = x_33;
x_19 = x_34;
x_20 = x_36;
x_21 = x_35;
x_22 = x_39;
x_23 = x_45;
goto block_30;
}
else
{
size_t x_46; size_t x_47; uint8_t x_48; 
x_46 = lean_ptr_addr(x_32);
lean_dec(x_32);
x_47 = lean_ptr_addr(x_36);
x_48 = lean_usize_dec_eq(x_46, x_47);
x_13 = x_37;
x_14 = x_41;
x_15 = x_38;
x_16 = x_40;
x_17 = x_42;
x_18 = x_33;
x_19 = x_34;
x_20 = x_36;
x_21 = x_35;
x_22 = x_39;
x_23 = x_48;
goto block_30;
}
}
block_197:
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_st_ref_get(x_2, x_11);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_array_get_size(x_56);
x_58 = lean_ptr_addr(x_1);
x_59 = lean_usize_to_uint64(x_58);
x_60 = 11;
x_61 = lean_uint64_mix_hash(x_59, x_60);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_56, x_72);
lean_dec(x_56);
x_74 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_73);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_free_object(x_52);
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_75 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0;
x_76 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_76);
x_77 = lean_mk_array(x_76, x_75);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_sub(x_76, x_78);
lean_dec(x_76);
x_80 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_81 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_80, x_50, x_51, x_1, x_1, x_77, x_79, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_82, x_2, x_3, x_4, x_5, x_6, x_83);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_84;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_81;
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
lean_dec(x_9);
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_86);
x_89 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_86, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Expr_hasLooseBVars(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_87);
x_93 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_87, x_2, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_31 = x_86;
x_32 = x_87;
x_33 = x_88;
x_34 = x_90;
x_35 = x_85;
x_36 = x_94;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_95;
goto block_49;
}
else
{
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_93;
}
}
else
{
lean_inc(x_87);
x_31 = x_86;
x_32 = x_87;
x_33 = x_88;
x_34 = x_90;
x_35 = x_85;
x_36 = x_87;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_91;
goto block_49;
}
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
case 10:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_9);
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_97);
x_98 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_97, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_102 = lean_ptr_addr(x_99);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Expr_mdata___override(x_96, x_99);
x_105 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_104, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_105;
}
else
{
lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_96);
lean_inc(x_1);
x_106 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_106;
}
}
else
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_98;
}
}
case 11:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_9);
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_109);
x_110 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_109, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ptr_addr(x_109);
lean_dec(x_109);
x_114 = lean_ptr_addr(x_111);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Expr_proj___override(x_107, x_108, x_111);
x_117 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_116, x_2, x_3, x_4, x_5, x_6, x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_107);
lean_inc(x_1);
x_118 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_118;
}
}
else
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_110;
}
}
default: 
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_9);
x_119 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_120 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(x_119, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_121, x_2, x_3, x_4, x_5, x_6, x_122);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_120;
}
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_74, 0);
lean_inc(x_124);
lean_dec(x_74);
lean_ctor_set(x_52, 0, x_124);
return x_52;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; size_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; size_t x_139; size_t x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
x_125 = lean_ctor_get(x_52, 0);
x_126 = lean_ctor_get(x_52, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_52);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_array_get_size(x_127);
x_129 = lean_ptr_addr(x_1);
x_130 = lean_usize_to_uint64(x_129);
x_131 = 11;
x_132 = lean_uint64_mix_hash(x_130, x_131);
x_133 = 32;
x_134 = lean_uint64_shift_right(x_132, x_133);
x_135 = lean_uint64_xor(x_132, x_134);
x_136 = 16;
x_137 = lean_uint64_shift_right(x_135, x_136);
x_138 = lean_uint64_xor(x_135, x_137);
x_139 = lean_uint64_to_usize(x_138);
x_140 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_141 = 1;
x_142 = lean_usize_sub(x_140, x_141);
x_143 = lean_usize_land(x_139, x_142);
x_144 = lean_array_uget(x_127, x_143);
lean_dec(x_127);
x_145 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_144);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_146 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0;
x_147 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_147);
x_148 = lean_mk_array(x_147, x_146);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_sub(x_147, x_149);
lean_dec(x_147);
x_151 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_152 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_151, x_50, x_51, x_1, x_1, x_148, x_150, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_153, x_2, x_3, x_4, x_5, x_6, x_154);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_155;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_152;
}
}
case 7:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
lean_dec(x_9);
x_156 = lean_ctor_get(x_1, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_1, 2);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_157);
x_160 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_157, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_Expr_hasLooseBVars(x_158);
if (x_163 == 0)
{
lean_object* x_164; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_158);
x_164 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_158, x_2, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_31 = x_157;
x_32 = x_158;
x_33 = x_159;
x_34 = x_161;
x_35 = x_156;
x_36 = x_165;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_166;
goto block_49;
}
else
{
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_164;
}
}
else
{
lean_inc(x_158);
x_31 = x_157;
x_32 = x_158;
x_33 = x_159;
x_34 = x_161;
x_35 = x_156;
x_36 = x_158;
x_37 = x_2;
x_38 = x_3;
x_39 = x_4;
x_40 = x_5;
x_41 = x_6;
x_42 = x_162;
goto block_49;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_160;
}
}
case 10:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_9);
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 1);
lean_inc(x_168);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_168);
x_169 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_168, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; size_t x_172; size_t x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ptr_addr(x_168);
lean_dec(x_168);
x_173 = lean_ptr_addr(x_170);
x_174 = lean_usize_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Expr_mdata___override(x_167, x_170);
x_176 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_175, x_2, x_3, x_4, x_5, x_6, x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_176;
}
else
{
lean_object* x_177; 
lean_dec(x_170);
lean_dec(x_167);
lean_inc(x_1);
x_177 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_177;
}
}
else
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_169;
}
}
case 11:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_9);
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_1, 2);
lean_inc(x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_180);
x_181 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_180, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; size_t x_184; size_t x_185; uint8_t x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ptr_addr(x_180);
lean_dec(x_180);
x_185 = lean_ptr_addr(x_182);
x_186 = lean_usize_dec_eq(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_Lean_Expr_proj___override(x_178, x_179, x_182);
x_188 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_187, x_2, x_3, x_4, x_5, x_6, x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_188;
}
else
{
lean_object* x_189; 
lean_dec(x_182);
lean_dec(x_179);
lean_dec(x_178);
lean_inc(x_1);
x_189 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_183);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_189;
}
}
else
{
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_181;
}
}
default: 
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_9);
x_190 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_191 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(x_190, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_192, x_2, x_3, x_4, x_5, x_6, x_193);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_194;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_191;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_145, 0);
lean_inc(x_195);
lean_dec(x_145);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_126);
return x_196;
}
}
}
block_202:
{
if (x_198 == 0)
{
uint8_t x_199; 
x_199 = l_Lean_Expr_isProj(x_1);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = l_Lean_Expr_isMData(x_1);
if (x_200 == 0)
{
lean_object* x_201; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_12)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_12;
}
lean_ctor_set(x_201, 0, x_1);
lean_ctor_set(x_201, 1, x_11);
return x_201;
}
else
{
lean_dec(x_12);
x_51 = x_200;
goto block_197;
}
}
else
{
lean_dec(x_12);
x_51 = x_199;
goto block_197;
}
}
else
{
lean_dec(x_12);
x_51 = x_198;
goto block_197;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_9);
x_205 = !lean_is_exclusive(x_8);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = lean_ctor_get(x_8, 1);
x_207 = lean_ctor_get(x_8, 0);
lean_dec(x_207);
x_208 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3;
x_209 = l_Lean_Expr_isAppOf(x_1, x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
lean_free_object(x_8);
x_210 = lean_st_ref_get(x_2, x_206);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; size_t x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; size_t x_226; size_t x_227; size_t x_228; size_t x_229; size_t x_230; lean_object* x_231; lean_object* x_232; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_array_get_size(x_214);
x_216 = lean_ptr_addr(x_1);
x_217 = lean_usize_to_uint64(x_216);
x_218 = 11;
x_219 = lean_uint64_mix_hash(x_217, x_218);
x_220 = 32;
x_221 = lean_uint64_shift_right(x_219, x_220);
x_222 = lean_uint64_xor(x_219, x_221);
x_223 = 16;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_xor(x_222, x_224);
x_226 = lean_uint64_to_usize(x_225);
x_227 = lean_usize_of_nat(x_215);
lean_dec(x_215);
x_228 = 1;
x_229 = lean_usize_sub(x_227, x_228);
x_230 = lean_usize_land(x_226, x_229);
x_231 = lean_array_uget(x_214, x_230);
lean_dec(x_214);
x_232 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_231);
lean_dec(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
lean_free_object(x_210);
x_233 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedProofsImpl_visit), 7, 0);
lean_inc(x_2);
lean_inc(x_1);
x_234 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(x_1, x_233, x_2, x_3, x_4, x_5, x_6, x_213);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_247; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_st_ref_take(x_2, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_247 = !lean_is_exclusive(x_238);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; size_t x_251; size_t x_252; size_t x_253; lean_object* x_254; uint8_t x_255; 
x_248 = lean_ctor_get(x_238, 0);
x_249 = lean_ctor_get(x_238, 1);
x_250 = lean_array_get_size(x_249);
x_251 = lean_usize_of_nat(x_250);
lean_dec(x_250);
x_252 = lean_usize_sub(x_251, x_228);
x_253 = lean_usize_land(x_226, x_252);
x_254 = lean_array_uget(x_249, x_253);
x_255 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_248, x_256);
lean_dec(x_248);
lean_inc(x_235);
x_258 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_258, 0, x_1);
lean_ctor_set(x_258, 1, x_235);
lean_ctor_set(x_258, 2, x_254);
x_259 = lean_array_uset(x_249, x_253, x_258);
x_260 = lean_unsigned_to_nat(4u);
x_261 = lean_nat_mul(x_257, x_260);
x_262 = lean_unsigned_to_nat(3u);
x_263 = lean_nat_div(x_261, x_262);
lean_dec(x_261);
x_264 = lean_array_get_size(x_259);
x_265 = lean_nat_dec_le(x_263, x_264);
lean_dec(x_264);
lean_dec(x_263);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_259);
lean_ctor_set(x_238, 1, x_266);
lean_ctor_set(x_238, 0, x_257);
x_240 = x_238;
goto block_246;
}
else
{
lean_ctor_set(x_238, 1, x_259);
lean_ctor_set(x_238, 0, x_257);
x_240 = x_238;
goto block_246;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_box(0);
x_268 = lean_array_uset(x_249, x_253, x_267);
lean_inc(x_235);
x_269 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_235, x_254);
x_270 = lean_array_uset(x_268, x_253, x_269);
lean_ctor_set(x_238, 1, x_270);
x_240 = x_238;
goto block_246;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; size_t x_274; size_t x_275; size_t x_276; lean_object* x_277; uint8_t x_278; 
x_271 = lean_ctor_get(x_238, 0);
x_272 = lean_ctor_get(x_238, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_238);
x_273 = lean_array_get_size(x_272);
x_274 = lean_usize_of_nat(x_273);
lean_dec(x_273);
x_275 = lean_usize_sub(x_274, x_228);
x_276 = lean_usize_land(x_226, x_275);
x_277 = lean_array_uget(x_272, x_276);
x_278 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_nat_add(x_271, x_279);
lean_dec(x_271);
lean_inc(x_235);
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_1);
lean_ctor_set(x_281, 1, x_235);
lean_ctor_set(x_281, 2, x_277);
x_282 = lean_array_uset(x_272, x_276, x_281);
x_283 = lean_unsigned_to_nat(4u);
x_284 = lean_nat_mul(x_280, x_283);
x_285 = lean_unsigned_to_nat(3u);
x_286 = lean_nat_div(x_284, x_285);
lean_dec(x_284);
x_287 = lean_array_get_size(x_282);
x_288 = lean_nat_dec_le(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_282);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_280);
lean_ctor_set(x_290, 1, x_289);
x_240 = x_290;
goto block_246;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_280);
lean_ctor_set(x_291, 1, x_282);
x_240 = x_291;
goto block_246;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_box(0);
x_293 = lean_array_uset(x_272, x_276, x_292);
lean_inc(x_235);
x_294 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_235, x_277);
x_295 = lean_array_uset(x_293, x_276, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_271);
lean_ctor_set(x_296, 1, x_295);
x_240 = x_296;
goto block_246;
}
}
block_246:
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_st_ref_set(x_2, x_240, x_239);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_241, 0);
lean_dec(x_243);
lean_ctor_set(x_241, 0, x_235);
return x_241;
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_235);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_234;
}
}
else
{
lean_object* x_297; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_ctor_get(x_232, 0);
lean_inc(x_297);
lean_dec(x_232);
lean_ctor_set(x_210, 0, x_297);
return x_210;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; size_t x_302; uint64_t x_303; uint64_t x_304; uint64_t x_305; uint64_t x_306; uint64_t x_307; uint64_t x_308; uint64_t x_309; uint64_t x_310; uint64_t x_311; size_t x_312; size_t x_313; size_t x_314; size_t x_315; size_t x_316; lean_object* x_317; lean_object* x_318; 
x_298 = lean_ctor_get(x_210, 0);
x_299 = lean_ctor_get(x_210, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_210);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_array_get_size(x_300);
x_302 = lean_ptr_addr(x_1);
x_303 = lean_usize_to_uint64(x_302);
x_304 = 11;
x_305 = lean_uint64_mix_hash(x_303, x_304);
x_306 = 32;
x_307 = lean_uint64_shift_right(x_305, x_306);
x_308 = lean_uint64_xor(x_305, x_307);
x_309 = 16;
x_310 = lean_uint64_shift_right(x_308, x_309);
x_311 = lean_uint64_xor(x_308, x_310);
x_312 = lean_uint64_to_usize(x_311);
x_313 = lean_usize_of_nat(x_301);
lean_dec(x_301);
x_314 = 1;
x_315 = lean_usize_sub(x_313, x_314);
x_316 = lean_usize_land(x_312, x_315);
x_317 = lean_array_uget(x_300, x_316);
lean_dec(x_300);
x_318 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_317);
lean_dec(x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedProofsImpl_visit), 7, 0);
lean_inc(x_2);
lean_inc(x_1);
x_320 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(x_1, x_319, x_2, x_3, x_4, x_5, x_6, x_299);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; size_t x_336; size_t x_337; size_t x_338; lean_object* x_339; uint8_t x_340; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_st_ref_take(x_2, x_322);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_332 = lean_ctor_get(x_324, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_324, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_334 = x_324;
} else {
 lean_dec_ref(x_324);
 x_334 = lean_box(0);
}
x_335 = lean_array_get_size(x_333);
x_336 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_337 = lean_usize_sub(x_336, x_314);
x_338 = lean_usize_land(x_312, x_337);
x_339 = lean_array_uget(x_333, x_338);
x_340 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_341 = lean_unsigned_to_nat(1u);
x_342 = lean_nat_add(x_332, x_341);
lean_dec(x_332);
lean_inc(x_321);
x_343 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_343, 0, x_1);
lean_ctor_set(x_343, 1, x_321);
lean_ctor_set(x_343, 2, x_339);
x_344 = lean_array_uset(x_333, x_338, x_343);
x_345 = lean_unsigned_to_nat(4u);
x_346 = lean_nat_mul(x_342, x_345);
x_347 = lean_unsigned_to_nat(3u);
x_348 = lean_nat_div(x_346, x_347);
lean_dec(x_346);
x_349 = lean_array_get_size(x_344);
x_350 = lean_nat_dec_le(x_348, x_349);
lean_dec(x_349);
lean_dec(x_348);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_344);
if (lean_is_scalar(x_334)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_334;
}
lean_ctor_set(x_352, 0, x_342);
lean_ctor_set(x_352, 1, x_351);
x_326 = x_352;
goto block_331;
}
else
{
lean_object* x_353; 
if (lean_is_scalar(x_334)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_334;
}
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_344);
x_326 = x_353;
goto block_331;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_box(0);
x_355 = lean_array_uset(x_333, x_338, x_354);
lean_inc(x_321);
x_356 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_321, x_339);
x_357 = lean_array_uset(x_355, x_338, x_356);
if (lean_is_scalar(x_334)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_334;
}
lean_ctor_set(x_358, 0, x_332);
lean_ctor_set(x_358, 1, x_357);
x_326 = x_358;
goto block_331;
}
block_331:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_st_ref_set(x_2, x_326, x_325);
lean_dec(x_2);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_329 = x_327;
} else {
 lean_dec_ref(x_327);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_321);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_320;
}
}
else
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_359 = lean_ctor_get(x_318, 0);
lean_inc(x_359);
lean_dec(x_318);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_299);
return x_360;
}
}
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
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = lean_ctor_get(x_8, 1);
lean_inc(x_361);
lean_dec(x_8);
x_362 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3;
x_363 = l_Lean_Expr_isAppOf(x_1, x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; size_t x_370; uint64_t x_371; uint64_t x_372; uint64_t x_373; uint64_t x_374; uint64_t x_375; uint64_t x_376; uint64_t x_377; uint64_t x_378; uint64_t x_379; size_t x_380; size_t x_381; size_t x_382; size_t x_383; size_t x_384; lean_object* x_385; lean_object* x_386; 
x_364 = lean_st_ref_get(x_2, x_361);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
x_369 = lean_array_get_size(x_368);
x_370 = lean_ptr_addr(x_1);
x_371 = lean_usize_to_uint64(x_370);
x_372 = 11;
x_373 = lean_uint64_mix_hash(x_371, x_372);
x_374 = 32;
x_375 = lean_uint64_shift_right(x_373, x_374);
x_376 = lean_uint64_xor(x_373, x_375);
x_377 = 16;
x_378 = lean_uint64_shift_right(x_376, x_377);
x_379 = lean_uint64_xor(x_376, x_378);
x_380 = lean_uint64_to_usize(x_379);
x_381 = lean_usize_of_nat(x_369);
lean_dec(x_369);
x_382 = 1;
x_383 = lean_usize_sub(x_381, x_382);
x_384 = lean_usize_land(x_380, x_383);
x_385 = lean_array_uget(x_368, x_384);
lean_dec(x_368);
x_386 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_385);
lean_dec(x_385);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_367);
x_387 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedProofsImpl_visit), 7, 0);
lean_inc(x_2);
lean_inc(x_1);
x_388 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(x_1, x_387, x_2, x_3, x_4, x_5, x_6, x_366);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; size_t x_404; size_t x_405; size_t x_406; lean_object* x_407; uint8_t x_408; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_st_ref_take(x_2, x_390);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_400 = lean_ctor_get(x_392, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_402 = x_392;
} else {
 lean_dec_ref(x_392);
 x_402 = lean_box(0);
}
x_403 = lean_array_get_size(x_401);
x_404 = lean_usize_of_nat(x_403);
lean_dec(x_403);
x_405 = lean_usize_sub(x_404, x_382);
x_406 = lean_usize_land(x_380, x_405);
x_407 = lean_array_uget(x_401, x_406);
x_408 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_409 = lean_unsigned_to_nat(1u);
x_410 = lean_nat_add(x_400, x_409);
lean_dec(x_400);
lean_inc(x_389);
x_411 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_411, 0, x_1);
lean_ctor_set(x_411, 1, x_389);
lean_ctor_set(x_411, 2, x_407);
x_412 = lean_array_uset(x_401, x_406, x_411);
x_413 = lean_unsigned_to_nat(4u);
x_414 = lean_nat_mul(x_410, x_413);
x_415 = lean_unsigned_to_nat(3u);
x_416 = lean_nat_div(x_414, x_415);
lean_dec(x_414);
x_417 = lean_array_get_size(x_412);
x_418 = lean_nat_dec_le(x_416, x_417);
lean_dec(x_417);
lean_dec(x_416);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_412);
if (lean_is_scalar(x_402)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_402;
}
lean_ctor_set(x_420, 0, x_410);
lean_ctor_set(x_420, 1, x_419);
x_394 = x_420;
goto block_399;
}
else
{
lean_object* x_421; 
if (lean_is_scalar(x_402)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_402;
}
lean_ctor_set(x_421, 0, x_410);
lean_ctor_set(x_421, 1, x_412);
x_394 = x_421;
goto block_399;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_422 = lean_box(0);
x_423 = lean_array_uset(x_401, x_406, x_422);
lean_inc(x_389);
x_424 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_389, x_407);
x_425 = lean_array_uset(x_423, x_406, x_424);
if (lean_is_scalar(x_402)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_402;
}
lean_ctor_set(x_426, 0, x_400);
lean_ctor_set(x_426, 1, x_425);
x_394 = x_426;
goto block_399;
}
block_399:
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_st_ref_set(x_2, x_394, x_393);
lean_dec(x_2);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_397 = x_395;
} else {
 lean_dec_ref(x_395);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_389);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_388;
}
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_427 = lean_ctor_get(x_386, 0);
lean_inc(x_427);
lean_dec(x_386);
if (lean_is_scalar(x_367)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_367;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_366);
return x_428;
}
}
else
{
lean_object* x_429; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_1);
lean_ctor_set(x_429, 1, x_361);
return x_429;
}
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_8);
if (x_430 == 0)
{
return x_8;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_8, 0);
x_432 = lean_ctor_get(x_8, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_8);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_14, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedProofsImpl___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrMap___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl___closed__0;
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
lean_dec(x_9);
return x_11;
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
static lean_object* _init_l_Lean_Meta_Grind_markProof_unsafe__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedProofsImpl_visit), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl___closed__0;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Grind_markProof_unsafe__1___closed__0;
lean_inc(x_9);
x_12 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl(x_1, x_11, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_14);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markProof_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__0);
l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__1);
l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__2);
l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__3);
l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MarkNestedProofs_0__Lean_Meta_Grind_markNestedProofImpl___closed__4);
l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0 = _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__0);
l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1 = _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__1);
l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2 = _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__2);
l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3 = _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__3);
l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4 = _init_l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4();
lean_mark_persistent(l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4___closed__4);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__0);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__1);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__2);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__3);
l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4 = _init_l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl_visit___closed__4);
l_Lean_Meta_Grind_markNestedProofsImpl___closed__0 = _init_l_Lean_Meta_Grind_markNestedProofsImpl___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_markNestedProofsImpl___closed__0);
l_Lean_Meta_Grind_markProof_unsafe__1___closed__0 = _init_l_Lean_Meta_Grind_markProof_unsafe__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_markProof_unsafe__1___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
