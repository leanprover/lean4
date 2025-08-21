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
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1;
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__2;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5;
static lean_object* l_Lean_Meta_reduce___closed__0;
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object**);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reduce___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_array_get_size(x_37);
x_39 = lean_nat_dec_lt(x_8, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_7);
x_41 = lean_nat_dec_lt(x_8, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_22;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_array_fget_borrowed(x_7, x_8);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_42);
x_43 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_1, x_2, x_3, x_42, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_box(0);
x_47 = lean_array_fset(x_7, x_8, x_46);
x_48 = lean_array_fset(x_47, x_8, x_44);
x_15 = x_48;
x_16 = x_45;
goto block_22;
}
else
{
uint8_t x_49; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
if (x_1 == 0)
{
goto block_36;
}
else
{
if (x_5 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_array_fget_borrowed(x_37, x_8);
x_54 = l_Lean_Meta_ParamInfo_isExplicit(x_53);
if (x_54 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_22;
}
else
{
goto block_36;
}
}
else
{
goto block_36;
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
x_19 = lean_nat_dec_lt(x_18, x_6);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
x_7 = x_15;
x_8 = x_18;
x_14 = x_16;
goto _start;
}
}
block_36:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_7);
x_24 = lean_nat_dec_lt(x_8, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget_borrowed(x_7, x_8);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_25);
x_26 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_1, x_2, x_3, x_25, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_7, x_8, x_29);
x_31 = lean_array_fset(x_30, x_8, x_27);
x_15 = x_31;
x_16 = x_28;
goto block_22;
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_12, x_13, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = 1;
x_12 = 0;
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_11, x_12, x_11, x_12, x_13, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_11, x_12, x_1, x_10, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get(x_5, 6);
x_22 = lean_ctor_get(x_5, 7);
x_23 = lean_ctor_get(x_5, 8);
x_24 = lean_ctor_get(x_5, 9);
x_25 = lean_ctor_get(x_5, 10);
x_26 = lean_ctor_get(x_5, 11);
x_27 = lean_ctor_get(x_5, 12);
x_28 = lean_nat_dec_eq(x_18, x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_18, x_29);
lean_dec(x_18);
lean_ctor_set(x_5, 3, x_30);
x_31 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_8 = x_31;
goto block_13;
}
else
{
lean_object* x_32; 
lean_free_object(x_5);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_32 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg(x_20, x_7);
x_8 = x_32;
goto block_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
x_35 = lean_ctor_get(x_5, 2);
x_36 = lean_ctor_get(x_5, 3);
x_37 = lean_ctor_get(x_5, 4);
x_38 = lean_ctor_get(x_5, 5);
x_39 = lean_ctor_get(x_5, 6);
x_40 = lean_ctor_get(x_5, 7);
x_41 = lean_ctor_get(x_5, 8);
x_42 = lean_ctor_get(x_5, 9);
x_43 = lean_ctor_get(x_5, 10);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_45 = lean_ctor_get(x_5, 11);
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_47 = lean_ctor_get(x_5, 12);
lean_inc(x_47);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_48 = lean_nat_dec_eq(x_36, x_37);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_36, x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
lean_ctor_set(x_51, 2, x_35);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_37);
lean_ctor_set(x_51, 5, x_38);
lean_ctor_set(x_51, 6, x_39);
lean_ctor_set(x_51, 7, x_40);
lean_ctor_set(x_51, 8, x_41);
lean_ctor_set(x_51, 9, x_42);
lean_ctor_set(x_51, 10, x_43);
lean_ctor_set(x_51, 11, x_45);
lean_ctor_set(x_51, 12, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*13, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*13 + 1, x_46);
x_52 = lean_apply_6(x_1, x_2, x_3, x_4, x_51, x_6, x_7);
x_8 = x_52;
goto block_13;
}
else
{
lean_object* x_53; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_53 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg(x_38, x_7);
x_8 = x_53;
goto block_13;
}
}
block_13:
{
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8_spec__8___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8_spec__8___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = 1;
x_18 = l_Lean_Meta_mkLambdaFVars(x_6, x_15, x_4, x_5, x_4, x_5, x_17, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_18;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_6, x_15, x_4, x_5, x_5, x_17, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_18;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(23u);
x_4 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1;
x_5 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5;
x_2 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_108; 
if (x_3 == 0)
{
x_108 = x_10;
goto block_123;
}
else
{
lean_object* x_124; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_124 = l_Lean_Meta_isType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec_ref(x_124);
x_108 = x_127;
goto block_123;
}
else
{
uint8_t x_128; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_124, 0);
lean_dec(x_129);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_dec(x_124);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_1);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
return x_124;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_124, 0);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_124);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_mkAppN(x_12, x_11);
lean_dec_ref(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = l_Lean_mkRawNatLit(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
block_36:
{
if (x_27 == 0)
{
x_11 = x_25;
x_12 = x_24;
x_13 = x_26;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = l_Lean_instInhabitedExpr;
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_borrowed(x_28, x_25, x_29);
x_31 = l_Lean_Expr_isRawNatLit(x_30);
if (x_31 == 0)
{
x_11 = x_25;
x_12 = x_24;
x_13 = x_26;
goto block_16;
}
else
{
lean_object* x_32; 
lean_inc_ref(x_30);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_32 = l_Lean_Expr_rawNatLit_x3f(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3;
x_34 = l_panic___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(x_33);
x_17 = x_26;
x_18 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_17 = x_26;
x_18 = x_35;
goto block_23;
}
}
}
}
block_45:
{
lean_object* x_40; uint8_t x_41; 
x_40 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6;
x_41 = l_Lean_Expr_isConstOf(x_37, x_40);
if (x_41 == 0)
{
x_24 = x_37;
x_25 = x_38;
x_26 = x_39;
x_27 = x_41;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_array_get_size(x_38);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
x_24 = x_37;
x_25 = x_38;
x_26 = x_39;
x_27 = x_44;
goto block_36;
}
}
block_107:
{
lean_object* x_49; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_49 = lean_whnf(x_1, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
switch (lean_obj_tag(x_50)) {
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Lean_Expr_getAppFn(x_50);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_53 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_2, x_3, x_4, x_52, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_56);
lean_inc(x_54);
x_57 = l_Lean_Meta_getFunInfoNArgs(x_54, x_56, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7;
lean_inc(x_56);
x_61 = lean_mk_array(x_56, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_56, x_62);
lean_dec(x_56);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_61, x_63);
x_65 = lean_array_get_size(x_64);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
if (x_67 == 0)
{
lean_dec(x_65);
lean_dec(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_37 = x_54;
x_38 = x_64;
x_39 = x_59;
goto block_45;
}
else
{
lean_object* x_68; 
x_68 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(x_2, x_3, x_4, x_58, x_47, x_65, x_64, x_66, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_65);
lean_dec(x_58);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_37 = x_54;
x_38 = x_69;
x_39 = x_70;
goto block_45;
}
else
{
uint8_t x_71; 
lean_dec(x_54);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
return x_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_53;
}
}
case 6:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_49, 1);
lean_inc(x_79);
lean_dec_ref(x_49);
x_80 = lean_box(x_2);
x_81 = lean_box(x_3);
x_82 = lean_box(x_4);
x_83 = lean_box(x_47);
x_84 = lean_box(x_46);
x_85 = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(x_85, 0, x_80);
lean_closure_set(x_85, 1, x_81);
lean_closure_set(x_85, 2, x_82);
lean_closure_set(x_85, 3, x_83);
lean_closure_set(x_85, 4, x_84);
x_86 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(x_50, x_85, x_47, x_5, x_6, x_7, x_8, x_9, x_79);
return x_86;
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_49, 1);
lean_inc(x_87);
lean_dec_ref(x_49);
x_88 = lean_box(x_2);
x_89 = lean_box(x_3);
x_90 = lean_box(x_4);
x_91 = lean_box(x_47);
x_92 = lean_box(x_46);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(x_93, 0, x_88);
lean_closure_set(x_93, 1, x_89);
lean_closure_set(x_93, 2, x_90);
lean_closure_set(x_93, 3, x_91);
lean_closure_set(x_93, 4, x_92);
x_94 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(x_50, x_93, x_47, x_5, x_6, x_7, x_8, x_9, x_87);
return x_94;
}
case 11:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_49, 1);
lean_inc(x_95);
lean_dec_ref(x_49);
x_96 = lean_ctor_get(x_50, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_50, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_50, 2);
lean_inc_ref(x_98);
lean_dec_ref(x_50);
x_99 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_2, x_3, x_4, x_98, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = l_Lean_Expr_proj___override(x_96, x_97, x_101);
lean_ctor_set(x_99, 0, x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = l_Lean_Expr_proj___override(x_96, x_97, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_dec(x_97);
lean_dec(x_96);
return x_99;
}
}
default: 
{
lean_dec(x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_49;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_49;
}
}
block_123:
{
uint8_t x_109; 
x_109 = 1;
if (x_4 == 0)
{
x_46 = x_109;
x_47 = x_4;
x_48 = x_108;
goto block_107;
}
else
{
lean_object* x_110; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_110 = l_Lean_Meta_isProof(x_1, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec_ref(x_110);
x_114 = lean_unbox(x_111);
lean_dec(x_111);
x_46 = x_109;
x_47 = x_114;
x_48 = x_113;
goto block_107;
}
else
{
uint8_t x_115; 
lean_dec(x_111);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_110, 0);
lean_dec(x_116);
lean_ctor_set(x_110, 0, x_1);
return x_110;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_110);
if (x_119 == 0)
{
return x_110;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_110, 0);
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_110);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc_ref(x_15);
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
lean_dec_ref(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(x_4, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_11);
x_31 = lean_box(x_1);
x_32 = lean_box(x_2);
x_33 = lean_box(x_3);
lean_inc_ref(x_4);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 10, 4);
lean_closure_set(x_34, 0, x_4);
lean_closure_set(x_34, 1, x_31);
lean_closure_set(x_34, 2, x_32);
lean_closure_set(x_34, 3, x_33);
lean_inc(x_5);
x_35 = l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(x_34, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_48; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_st_ref_take(x_5, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
x_51 = lean_array_get_size(x_50);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_sub(x_52, x_26);
x_54 = lean_usize_land(x_24, x_53);
x_55 = lean_array_uget(x_50, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(x_4, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_49, x_57);
lean_dec(x_49);
lean_inc(x_36);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_36);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_50, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(x_60);
lean_ctor_set(x_39, 1, x_67);
lean_ctor_set(x_39, 0, x_58);
x_41 = x_39;
goto block_47;
}
else
{
lean_ctor_set(x_39, 1, x_60);
lean_ctor_set(x_39, 0, x_58);
x_41 = x_39;
goto block_47;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_50, x_54, x_68);
lean_inc(x_36);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_4, x_36, x_55);
x_71 = lean_array_uset(x_69, x_54, x_70);
lean_ctor_set(x_39, 1, x_71);
x_41 = x_39;
goto block_47;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_72 = lean_ctor_get(x_39, 0);
x_73 = lean_ctor_get(x_39, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_39);
x_74 = lean_array_get_size(x_73);
x_75 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_76 = lean_usize_sub(x_75, x_26);
x_77 = lean_usize_land(x_24, x_76);
x_78 = lean_array_uget(x_73, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(x_4, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_72, x_80);
lean_dec(x_72);
lean_inc(x_36);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_4);
lean_ctor_set(x_82, 1, x_36);
lean_ctor_set(x_82, 2, x_78);
x_83 = lean_array_uset(x_73, x_77, x_82);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_nat_mul(x_81, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_div(x_85, x_86);
lean_dec(x_85);
x_88 = lean_array_get_size(x_83);
x_89 = lean_nat_dec_le(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
x_41 = x_91;
goto block_47;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_83);
x_41 = x_92;
goto block_47;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_box(0);
x_94 = lean_array_uset(x_73, x_77, x_93);
lean_inc(x_36);
x_95 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_4, x_36, x_78);
x_96 = lean_array_uset(x_94, x_77, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_72);
lean_ctor_set(x_97, 1, x_96);
x_41 = x_97;
goto block_47;
}
}
block_47:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_set(x_5, x_41, x_40);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_36);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_35;
}
}
else
{
lean_object* x_98; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_98 = lean_ctor_get(x_30, 0);
lean_inc(x_98);
lean_dec_ref(x_30);
lean_ctor_set(x_11, 0, x_98);
return x_11;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_99 = lean_ctor_get(x_11, 0);
x_100 = lean_ctor_get(x_11, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_11);
x_101 = lean_ctor_get(x_99, 1);
lean_inc_ref(x_101);
lean_dec(x_99);
x_102 = lean_array_get_size(x_101);
x_103 = l_Lean_Expr_hash(x_4);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_101, x_114);
lean_dec_ref(x_101);
x_116 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(x_4, x_115);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_box(x_1);
x_118 = lean_box(x_2);
x_119 = lean_box(x_3);
lean_inc_ref(x_4);
x_120 = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 10, 4);
lean_closure_set(x_120, 0, x_4);
lean_closure_set(x_120, 1, x_117);
lean_closure_set(x_120, 2, x_118);
lean_closure_set(x_120, 3, x_119);
lean_inc(x_5);
x_121 = l_Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(x_120, x_5, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; size_t x_137; size_t x_138; size_t x_139; lean_object* x_140; uint8_t x_141; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_st_ref_take(x_5, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_133 = lean_ctor_get(x_125, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_134);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_135 = x_125;
} else {
 lean_dec_ref(x_125);
 x_135 = lean_box(0);
}
x_136 = lean_array_get_size(x_134);
x_137 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_138 = lean_usize_sub(x_137, x_112);
x_139 = lean_usize_land(x_110, x_138);
x_140 = lean_array_uget(x_134, x_139);
x_141 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(x_4, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_133, x_142);
lean_dec(x_133);
lean_inc(x_122);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_4);
lean_ctor_set(x_144, 1, x_122);
lean_ctor_set(x_144, 2, x_140);
x_145 = lean_array_uset(x_134, x_139, x_144);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_mul(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__8___redArg(x_145);
if (lean_is_scalar(x_135)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_135;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_127 = x_153;
goto block_132;
}
else
{
lean_object* x_154; 
if (lean_is_scalar(x_135)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_135;
}
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_145);
x_127 = x_154;
goto block_132;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_box(0);
x_156 = lean_array_uset(x_134, x_139, x_155);
lean_inc(x_122);
x_157 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__11___redArg(x_4, x_122, x_140);
x_158 = lean_array_uset(x_156, x_139, x_157);
if (lean_is_scalar(x_135)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_135;
}
lean_ctor_set(x_159, 0, x_133);
lean_ctor_set(x_159, 1, x_158);
x_127 = x_159;
goto block_132;
}
block_132:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_st_ref_set(x_5, x_127, x_126);
lean_dec(x_5);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_121;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_160 = lean_ctor_get(x_116, 0);
lean_inc(x_160);
lean_dec_ref(x_116);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_100);
return x_161;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_unbox(x_1);
x_16 = lean_unbox(x_2);
x_17 = lean_unbox(x_3);
x_18 = lean_unbox(x_5);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(x_15, x_16, x_17, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_unbox(x_1);
x_23 = lean_unbox(x_2);
x_24 = lean_unbox(x_3);
x_25 = lean_unbox(x_5);
x_26 = lean_unbox(x_6);
x_27 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(x_22, x_23, x_24, x_4, x_25, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(x_14, x_15, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(x_14, x_15, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(x_1, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_reduce___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reduce___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduce___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_reduce___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_reduce___closed__4;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_12);
x_14 = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(x_2, x_3, x_4, x_1, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
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
lean_dec(x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox(x_4);
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
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at_____private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__5___redArg___closed__6);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6);
l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7 = _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7);
l_Lean_Meta_reduce___closed__0 = _init_l_Lean_Meta_reduce___closed__0();
lean_mark_persistent(l_Lean_Meta_reduce___closed__0);
l_Lean_Meta_reduce___closed__1 = _init_l_Lean_Meta_reduce___closed__1();
lean_mark_persistent(l_Lean_Meta_reduce___closed__1);
l_Lean_Meta_reduce___closed__2 = _init_l_Lean_Meta_reduce___closed__2();
lean_mark_persistent(l_Lean_Meta_reduce___closed__2);
l_Lean_Meta_reduce___closed__3 = _init_l_Lean_Meta_reduce___closed__3();
lean_mark_persistent(l_Lean_Meta_reduce___closed__3);
l_Lean_Meta_reduce___closed__4 = _init_l_Lean_Meta_reduce___closed__4();
lean_mark_persistent(l_Lean_Meta_reduce___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
