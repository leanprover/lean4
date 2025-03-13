// Lean compiler output
// Module: Lean.Meta.Reduce
// Imports: Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.MonadCache
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6;
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__6;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__4(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9___boxed(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__3;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_reduce_visit___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__2;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__3(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__2(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_reduce_visit___spec__12(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_reduce_visit___spec__10(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_reduce_visit___lambda__4___closed__8;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_nat_dec_lt(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_8, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_array_get_size(x_7);
x_31 = lean_nat_dec_lt(x_8, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_7);
x_20 = x_32;
x_21 = x_16;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_array_fget(x_7, x_8);
x_34 = lean_box(0);
x_35 = lean_array_fset(x_7, x_8, x_34);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_33, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_fset(x_35, x_8, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_20 = x_40;
x_21 = x_38;
goto block_26;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
if (x_1 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_array_get_size(x_7);
x_46 = lean_nat_dec_lt(x_8, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_20 = x_47;
x_21 = x_16;
goto block_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_array_fget(x_7, x_8);
x_49 = lean_box(0);
x_50 = lean_array_fset(x_7, x_8, x_49);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_51 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_48, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_array_fset(x_50, x_8, x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_20 = x_55;
x_21 = x_53;
goto block_26;
}
else
{
uint8_t x_56; 
lean_dec(x_50);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_array_fget(x_27, x_8);
x_61 = l_Lean_Meta_ParamInfo_isExplicit(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_7);
x_20 = x_62;
x_21 = x_16;
goto block_26;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_array_get_size(x_7);
x_64 = lean_nat_dec_lt(x_8, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_7);
x_20 = x_65;
x_21 = x_16;
goto block_26;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_array_fget(x_7, x_8);
x_67 = lean_box(0);
x_68 = lean_array_fset(x_7, x_8, x_67);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_69 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_66, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_array_fset(x_68, x_8, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_20 = x_73;
x_21 = x_71;
goto block_26;
}
else
{
uint8_t x_74; 
lean_dec(x_68);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_74 = !lean_is_exclusive(x_69);
if (x_74 == 0)
{
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_nat_add(x_8, x_23);
lean_dec(x_8);
x_7 = x_22;
x_8 = x_24;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_16 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_12, x_11, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_12, x_11, x_1, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 10);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_20 = lean_ctor_get(x_5, 11);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
x_22 = lean_nat_dec_eq(x_11, x_12);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_5, 11);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 10);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 9);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 8);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 7);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 6);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 5);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 4);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 3);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 0);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_11, x_36);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_37);
x_38 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_11, x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_9);
lean_ctor_set(x_49, 2, x_10);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_12);
lean_ctor_set(x_49, 5, x_13);
lean_ctor_set(x_49, 6, x_14);
lean_ctor_set(x_49, 7, x_15);
lean_ctor_set(x_49, 8, x_16);
lean_ctor_set(x_49, 9, x_17);
lean_ctor_set(x_49, 10, x_18);
lean_ctor_set(x_49, 11, x_20);
lean_ctor_set_uint8(x_49, sizeof(void*)*12, x_19);
lean_ctor_set_uint8(x_49, sizeof(void*)*12 + 1, x_21);
x_50 = lean_apply_6(x_1, x_2, x_3, x_4, x_49, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8(x_13, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_reduce_visit___spec__12(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_reduce_visit___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_reduce_visit___spec__12(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_reduce_visit___spec__10(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_reduce_visit___spec__11(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_box(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isType(x_1, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__2(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = 1;
x_17 = 1;
x_18 = l_Lean_Meta_mkLambdaFVars(x_4, x_13, x_15, x_16, x_15, x_17, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__3(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = 1;
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_4, x_13, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduce_visit___lambda__4___closed__2;
x_2 = l_Lean_Meta_reduce_visit___lambda__4___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reduce_visit___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_reduce_visit___lambda__4___closed__5;
x_2 = l_Lean_Meta_reduce_visit___lambda__4___closed__6;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Meta_reduce_visit___lambda__4___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_5 == 0)
{
uint8_t x_12; lean_object* x_13; 
if (x_4 == 0)
{
x_12 = x_4;
x_13 = x_11;
goto block_130;
}
else
{
lean_object* x_131; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_131 = l_Lean_Meta_isProof(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_unbox(x_132);
lean_dec(x_132);
x_12 = x_134;
x_13 = x_133;
goto block_130;
}
else
{
uint8_t x_135; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_131);
if (x_135 == 0)
{
return x_131;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_131);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
block_130:
{
if (x_12 == 0)
{
lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = lean_whnf(x_1, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_getAppFn(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_reduce_visit(x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_15, x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_19);
x_23 = l_Lean_Meta_getFunInfoNArgs(x_19, x_22, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_reduce_visit___lambda__4___closed__1;
lean_inc(x_22);
x_27 = lean_mk_array(x_22, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_22, x_28);
lean_dec(x_22);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_27, x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
x_33 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4(x_2, x_3, x_4, x_24, x_32, x_32, x_30, x_21, lean_box(0), lean_box(0), x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_32);
lean_dec(x_24);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lean_Meta_reduce_visit___lambda__4___closed__4;
x_37 = l_Lean_Expr_isConstOf(x_19, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_mkAppN(x_19, x_35);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_get_size(x_35);
x_40 = lean_nat_dec_eq(x_39, x_28);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_mkAppN(x_19, x_35);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_instInhabitedExpr;
x_43 = lean_array_get(x_42, x_35, x_21);
x_44 = l_Lean_Expr_isRawNatLit(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l_Lean_mkAppN(x_19, x_35);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_45);
return x_33;
}
else
{
lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_19);
x_46 = l_Lean_Expr_rawNatLit_x3f(x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Meta_reduce_visit___lambda__4___closed__8;
x_48 = l_panic___at_String_toNat_x21___spec__1(x_47);
x_49 = lean_nat_add(x_48, x_28);
lean_dec(x_48);
x_50 = l_Lean_mkRawNatLit(x_49);
lean_ctor_set(x_33, 0, x_50);
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_nat_add(x_51, x_28);
lean_dec(x_51);
x_53 = l_Lean_mkRawNatLit(x_52);
lean_ctor_set(x_33, 0, x_53);
return x_33;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = l_Lean_Meta_reduce_visit___lambda__4___closed__4;
x_57 = l_Lean_Expr_isConstOf(x_19, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_mkAppN(x_19, x_54);
lean_dec(x_54);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_array_get_size(x_54);
x_61 = lean_nat_dec_eq(x_60, x_28);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_mkAppN(x_19, x_54);
lean_dec(x_54);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Lean_instInhabitedExpr;
x_65 = lean_array_get(x_64, x_54, x_21);
x_66 = l_Lean_Expr_isRawNatLit(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
x_67 = l_Lean_mkAppN(x_19, x_54);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_54);
lean_dec(x_19);
x_69 = l_Lean_Expr_rawNatLit_x3f(x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = l_Lean_Meta_reduce_visit___lambda__4___closed__8;
x_71 = l_panic___at_String_toNat_x21___spec__1(x_70);
x_72 = lean_nat_add(x_71, x_28);
lean_dec(x_71);
x_73 = l_Lean_mkRawNatLit(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_55);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_nat_add(x_75, x_28);
lean_dec(x_75);
x_77 = l_Lean_mkRawNatLit(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_55);
return x_78;
}
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_19);
x_79 = !lean_is_exclusive(x_33);
if (x_79 == 0)
{
return x_33;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_33, 0);
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_33);
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
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_23);
if (x_83 == 0)
{
return x_23;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_23, 0);
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_23);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_18);
if (x_87 == 0)
{
return x_18;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
case 6:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
lean_dec(x_14);
x_92 = lean_box(x_2);
x_93 = lean_box(x_3);
x_94 = lean_box(x_4);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__2___boxed), 11, 3);
lean_closure_set(x_95, 0, x_92);
lean_closure_set(x_95, 1, x_93);
lean_closure_set(x_95, 2, x_94);
x_96 = 0;
x_97 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(x_15, x_95, x_96, x_6, x_7, x_8, x_9, x_10, x_91);
return x_97;
}
case 7:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_14, 1);
lean_inc(x_98);
lean_dec(x_14);
x_99 = lean_box(x_2);
x_100 = lean_box(x_3);
x_101 = lean_box(x_4);
x_102 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__3___boxed), 11, 3);
lean_closure_set(x_102, 0, x_99);
lean_closure_set(x_102, 1, x_100);
lean_closure_set(x_102, 2, x_101);
x_103 = 0;
x_104 = l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg(x_15, x_102, x_103, x_6, x_7, x_8, x_9, x_10, x_98);
return x_104;
}
case 11:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_14, 1);
lean_inc(x_105);
lean_dec(x_14);
x_106 = lean_ctor_get(x_15, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_15, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_15, 2);
lean_inc(x_108);
lean_dec(x_15);
x_109 = l_Lean_Meta_reduce_visit(x_2, x_3, x_4, x_108, x_6, x_7, x_8, x_9, x_10, x_105);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = l_Lean_Expr_proj___override(x_106, x_107, x_111);
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = l_Lean_Expr_proj___override(x_106, x_107, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_107);
lean_dec(x_106);
x_117 = !lean_is_exclusive(x_109);
if (x_117 == 0)
{
return x_109;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_109, 0);
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
default: 
{
uint8_t x_121; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_121 = !lean_is_exclusive(x_14);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_14, 0);
lean_dec(x_122);
return x_14;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
lean_dec(x_14);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_15);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_125 = !lean_is_exclusive(x_14);
if (x_125 == 0)
{
return x_14;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_14, 0);
x_127 = lean_ctor_get(x_14, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_14);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_13);
return x_129;
}
}
}
else
{
lean_object* x_139; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_11);
return x_139;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Expr_hash(x_4);
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
lean_dec(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1(x_4, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_11);
x_31 = lean_box(x_2);
x_32 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg___boxed), 7, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_4);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__1___boxed), 8, 1);
lean_closure_set(x_33, 0, x_4);
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg), 8, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_box(x_1);
x_36 = lean_box(x_2);
x_37 = lean_box(x_3);
lean_inc(x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__4___boxed), 11, 4);
lean_closure_set(x_38, 0, x_4);
lean_closure_set(x_38, 1, x_35);
lean_closure_set(x_38, 2, x_36);
lean_closure_set(x_38, 3, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg), 8, 2);
lean_closure_set(x_39, 0, x_34);
lean_closure_set(x_39, 1, x_38);
lean_inc(x_5);
x_40 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__7(x_39, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_take(x_5, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = lean_usize_sub(x_50, x_26);
x_52 = lean_usize_land(x_24, x_51);
x_53 = lean_array_uget(x_48, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(x_4, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_47, x_55);
lean_dec(x_47);
lean_inc(x_41);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_53);
x_58 = lean_array_uset(x_48, x_52, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_reduce_visit___spec__10(x_58);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_56);
x_66 = lean_st_ref_set(x_5, x_44, x_45);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_41);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_41);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_ctor_set(x_44, 1, x_58);
lean_ctor_set(x_44, 0, x_56);
x_71 = lean_st_ref_set(x_5, x_44, x_45);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_41);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_box(0);
x_77 = lean_array_uset(x_48, x_52, x_76);
lean_inc(x_41);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(x_4, x_41, x_53);
x_79 = lean_array_uset(x_77, x_52, x_78);
lean_ctor_set(x_44, 1, x_79);
x_80 = lean_st_ref_set(x_5, x_44, x_45);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set(x_80, 0, x_41);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_85 = lean_ctor_get(x_44, 0);
x_86 = lean_ctor_get(x_44, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_44);
x_87 = lean_array_get_size(x_86);
x_88 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_89 = lean_usize_sub(x_88, x_26);
x_90 = lean_usize_land(x_24, x_89);
x_91 = lean_array_uget(x_86, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(x_4, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_85, x_93);
lean_dec(x_85);
lean_inc(x_41);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_95, 1, x_41);
lean_ctor_set(x_95, 2, x_91);
x_96 = lean_array_uset(x_86, x_90, x_95);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_mul(x_94, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_div(x_98, x_99);
lean_dec(x_98);
x_101 = lean_array_get_size(x_96);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_reduce_visit___spec__10(x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_st_ref_set(x_5, x_104, x_45);
lean_dec(x_5);
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
lean_ctor_set(x_108, 0, x_41);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_94);
lean_ctor_set(x_109, 1, x_96);
x_110 = lean_st_ref_set(x_5, x_109, x_45);
lean_dec(x_5);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_41);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_box(0);
x_115 = lean_array_uset(x_86, x_90, x_114);
lean_inc(x_41);
x_116 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(x_4, x_41, x_91);
x_117 = lean_array_uset(x_115, x_90, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_85);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_st_ref_set(x_5, x_118, x_45);
lean_dec(x_5);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_41);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_5);
lean_dec(x_4);
x_123 = !lean_is_exclusive(x_40);
if (x_123 == 0)
{
return x_40;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_40, 0);
x_125 = lean_ctor_get(x_40, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_40);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = lean_ctor_get(x_30, 0);
lean_inc(x_127);
lean_dec(x_30);
lean_ctor_set(x_11, 0, x_127);
return x_11;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; size_t x_139; size_t x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
x_128 = lean_ctor_get(x_11, 0);
x_129 = lean_ctor_get(x_11, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_11);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_array_get_size(x_130);
x_132 = l_Lean_Expr_hash(x_4);
x_133 = 32;
x_134 = lean_uint64_shift_right(x_132, x_133);
x_135 = lean_uint64_xor(x_132, x_134);
x_136 = 16;
x_137 = lean_uint64_shift_right(x_135, x_136);
x_138 = lean_uint64_xor(x_135, x_137);
x_139 = lean_uint64_to_usize(x_138);
x_140 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_141 = 1;
x_142 = lean_usize_sub(x_140, x_141);
x_143 = lean_usize_land(x_139, x_142);
x_144 = lean_array_uget(x_130, x_143);
lean_dec(x_130);
x_145 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1(x_4, x_144);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_146 = lean_box(x_2);
x_147 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg___boxed), 7, 1);
lean_closure_set(x_147, 0, x_146);
lean_inc(x_4);
x_148 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__1___boxed), 8, 1);
lean_closure_set(x_148, 0, x_4);
x_149 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg), 8, 2);
lean_closure_set(x_149, 0, x_147);
lean_closure_set(x_149, 1, x_148);
x_150 = lean_box(x_1);
x_151 = lean_box(x_2);
x_152 = lean_box(x_3);
lean_inc(x_4);
x_153 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lambda__4___boxed), 11, 4);
lean_closure_set(x_153, 0, x_4);
lean_closure_set(x_153, 1, x_150);
lean_closure_set(x_153, 2, x_151);
lean_closure_set(x_153, 3, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__3___rarg), 8, 2);
lean_closure_set(x_154, 0, x_149);
lean_closure_set(x_154, 1, x_153);
lean_inc(x_5);
x_155 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__7(x_154, x_5, x_6, x_7, x_8, x_9, x_129);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; size_t x_165; size_t x_166; size_t x_167; lean_object* x_168; uint8_t x_169; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_st_ref_take(x_5, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
x_164 = lean_array_get_size(x_162);
x_165 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_166 = lean_usize_sub(x_165, x_141);
x_167 = lean_usize_land(x_139, x_166);
x_168 = lean_array_uget(x_162, x_167);
x_169 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(x_4, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_add(x_161, x_170);
lean_dec(x_161);
lean_inc(x_156);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_4);
lean_ctor_set(x_172, 1, x_156);
lean_ctor_set(x_172, 2, x_168);
x_173 = lean_array_uset(x_162, x_167, x_172);
x_174 = lean_unsigned_to_nat(4u);
x_175 = lean_nat_mul(x_171, x_174);
x_176 = lean_unsigned_to_nat(3u);
x_177 = lean_nat_div(x_175, x_176);
lean_dec(x_175);
x_178 = lean_array_get_size(x_173);
x_179 = lean_nat_dec_le(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_reduce_visit___spec__10(x_173);
if (lean_is_scalar(x_163)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_163;
}
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_st_ref_set(x_5, x_181, x_160);
lean_dec(x_5);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_156);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
if (lean_is_scalar(x_163)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_163;
}
lean_ctor_set(x_186, 0, x_171);
lean_ctor_set(x_186, 1, x_173);
x_187 = lean_st_ref_set(x_5, x_186, x_160);
lean_dec(x_5);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_156);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_191 = lean_box(0);
x_192 = lean_array_uset(x_162, x_167, x_191);
lean_inc(x_156);
x_193 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_reduce_visit___spec__13(x_4, x_156, x_168);
x_194 = lean_array_uset(x_192, x_167, x_193);
if (lean_is_scalar(x_163)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_163;
}
lean_ctor_set(x_195, 0, x_161);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_st_ref_set(x_5, x_195, x_160);
lean_dec(x_5);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_156);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_5);
lean_dec(x_4);
x_200 = lean_ctor_get(x_155, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_155, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_202 = x_155;
} else {
 lean_dec_ref(x_155);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_204 = lean_ctor_get(x_145, 0);
lean_inc(x_204);
lean_dec(x_145);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_129);
return x_205;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_reduce_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_reduce_visit___spec__4(x_17, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__6___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_reduce_visit___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_reduce_visit___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_reduce_visit___lambda__2(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_reduce_visit___lambda__3(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_reduce_visit___lambda__4(x_1, x_12, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_reduce_visit(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduce___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_reduce___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_reduce___closed__3;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Meta_reduce_visit(x_2, x_3, x_4, x_1, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_reduce(x_1, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_reduce(x_1, x_7, x_7, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_reduce_visit___spec__8___closed__6);
l_Lean_Meta_reduce_visit___lambda__4___closed__1 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__1);
l_Lean_Meta_reduce_visit___lambda__4___closed__2 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__2);
l_Lean_Meta_reduce_visit___lambda__4___closed__3 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__3);
l_Lean_Meta_reduce_visit___lambda__4___closed__4 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__4);
l_Lean_Meta_reduce_visit___lambda__4___closed__5 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__5);
l_Lean_Meta_reduce_visit___lambda__4___closed__6 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__6);
l_Lean_Meta_reduce_visit___lambda__4___closed__7 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__7);
l_Lean_Meta_reduce_visit___lambda__4___closed__8 = _init_l_Lean_Meta_reduce_visit___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Meta_reduce_visit___lambda__4___closed__8);
l_Lean_Meta_reduce___closed__1 = _init_l_Lean_Meta_reduce___closed__1();
lean_mark_persistent(l_Lean_Meta_reduce___closed__1);
l_Lean_Meta_reduce___closed__2 = _init_l_Lean_Meta_reduce___closed__2();
lean_mark_persistent(l_Lean_Meta_reduce___closed__2);
l_Lean_Meta_reduce___closed__3 = _init_l_Lean_Meta_reduce___closed__3();
lean_mark_persistent(l_Lean_Meta_reduce___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
