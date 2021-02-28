// Lean compiler output
// Module: Lean.Meta.Reduce
// Imports: Init Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.MonadCache
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
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo;
lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr___closed__1;
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce_visit_match__1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5(lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_3(x_2, x_6, x_7, x_9);
return x_10;
}
case 6:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_3, x_11, x_12, x_13, x_15);
return x_16;
}
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_21 = lean_box_uint64(x_20);
x_22 = lean_apply_4(x_4, x_17, x_18, x_19, x_21);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_apply_1(x_5, x_1);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_reduce_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___rarg), 8, 0);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isType(x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_nat_dec_le(x_15, x_7);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_6, x_19);
lean_dec(x_6);
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_7, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_array_get_size(x_8);
x_32 = lean_nat_dec_lt(x_7, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_8);
x_21 = x_33;
x_22 = x_14;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_array_fget(x_8, x_7);
x_35 = l_Lean_instInhabitedExpr___closed__1;
x_36 = lean_array_fset(x_8, x_7, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_34, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_fset(x_36, x_7, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_21 = x_41;
x_22 = x_39;
goto block_27;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
if (x_1 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_array_get_size(x_8);
x_47 = lean_nat_dec_lt(x_7, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_8);
x_21 = x_48;
x_22 = x_14;
goto block_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_array_fget(x_8, x_7);
x_50 = l_Lean_instInhabitedExpr___closed__1;
x_51 = lean_array_fset(x_8, x_7, x_50);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_49, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_array_fset(x_51, x_7, x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_21 = x_56;
x_22 = x_54;
goto block_27;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
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
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = l_Lean_Meta_instInhabitedParamInfo;
x_62 = lean_array_get(x_61, x_28, x_7);
x_63 = l_Lean_Meta_ParamInfo_isExplicit(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_8);
x_21 = x_64;
x_22 = x_14;
goto block_27;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_array_get_size(x_8);
x_66 = lean_nat_dec_lt(x_7, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_8);
x_21 = x_67;
x_22 = x_14;
goto block_27;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_array_fget(x_8, x_7);
x_69 = l_Lean_instInhabitedExpr___closed__1;
x_70 = lean_array_fset(x_8, x_7, x_69);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_71 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_68, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_array_fset(x_70, x_7, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_21 = x_75;
x_22 = x_73;
goto block_27;
}
else
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_5, 2);
x_25 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_25;
x_8 = x_23;
x_14 = x_22;
goto _start;
}
}
else
{
lean_object* x_80; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_14);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_8);
lean_ctor_set(x_81, 1, x_14);
return x_81;
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_6, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = 1;
x_17 = l_Lean_Meta_mkLambdaFVars(x_5, x_13, x_15, x_16, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_box(x_1);
x_13 = lean_box(x_2);
x_14 = lean_box(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1___boxed), 11, 4);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_6);
x_16 = 0;
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_5, x_16, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_box(0);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_11, x_10, x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_6, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = 1;
x_17 = l_Lean_Meta_mkForallFVars(x_5, x_13, x_15, x_16, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_box(x_1);
x_13 = lean_box(x_2);
x_14 = lean_box(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1___boxed), 11, 4);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_6);
x_16 = lean_box(0);
x_17 = 0;
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_17, x_16, x_5, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_12 = l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_64; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_64 = lean_unbox(x_13);
lean_dec(x_13);
if (x_64 == 0)
{
if (x_3 == 0)
{
x_16 = x_3;
x_17 = x_14;
goto block_63;
}
else
{
lean_object* x_65; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_65 = l_Lean_Meta_isProof(x_4, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_16 = x_68;
x_17 = x_67;
goto block_63;
}
else
{
uint8_t x_69; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 0);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_65);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_14);
return x_73;
}
block_63:
{
if (x_16 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_whnf(x_4, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_getAppFn(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux(x_19, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
lean_inc(x_21);
x_24 = l_Lean_Meta_getFunInfoNArgs(x_21, x_23, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_28 = lean_mk_array(x_23, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_23, x_29);
lean_dec(x_23);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_19, x_28, x_30);
x_32 = lean_array_get_size(x_31);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_29);
x_34 = l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4(x_1, x_2, x_3, x_25, x_33, x_32, x_22, x_31, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_33);
lean_dec(x_25);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_mkAppN(x_21, x_36);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = l_Lean_mkAppN(x_21, x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 6:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_dec(x_18);
x_51 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6(x_1, x_2, x_3, x_5, x_19, x_6, x_7, x_8, x_9, x_10, x_50);
return x_51;
}
case 7:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
x_53 = l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8(x_1, x_2, x_3, x_5, x_19, x_6, x_7, x_8, x_9, x_10, x_52);
return x_53;
}
default: 
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_18, 0);
lean_dec(x_55);
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_dec(x_18);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_19);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_15)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_15;
}
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_17);
return x_62;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
return x_12;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_12, 0);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_12);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
x_14 = lean_apply_6(x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_apply_6(x_2, x_3, x_4, x_5, x_22, x_8, x_9);
return x_23;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1(x_8, x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_22 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_21, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_15);
x_18 = l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 2);
x_21 = lean_ctor_get(x_11, 3);
x_22 = lean_ctor_get(x_11, 4);
x_23 = lean_ctor_get(x_11, 5);
x_24 = lean_ctor_get(x_11, 6);
x_25 = lean_ctor_get(x_11, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_22);
lean_ctor_set(x_26, 5, x_23);
lean_ctor_set(x_26, 6, x_24);
lean_ctor_set(x_26, 7, x_25);
x_27 = l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26, x_12, x_13);
return x_27;
}
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1(x_12, x_1, x_2, x_3, x_4, x_11, x_5, x_6, x_7, x_15, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_26 = l_Lean_throwError___at_Lean_Core_withIncRecDepth___spec__1(x_25, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_reduce_visit(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_15, x_4);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_13);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_9, x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_19);
x_26 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_24, x_4, x_19);
x_27 = lean_st_ref_set(x_5, x_26, x_25);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_37, x_4);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_9, x_42);
lean_dec(x_9);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_5, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_41);
x_48 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_46, x_4, x_41);
x_49 = lean_st_ref_set(x_5, x_48, x_47);
lean_dec(x_5);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
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
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_38);
return x_58;
}
}
}
}
lean_object* l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_pure___at_Lean_Meta_reduce_visit___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Std_Range_forIn_loop___at_Lean_Meta_reduce_visit___spec__4(x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___lambda__1(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_reduce_visit___spec__5___at_Lean_Meta_reduce_visit___spec__6(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___lambda__1(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_forallTelescope___at_Lean_Meta_reduce_visit___spec__7___at_Lean_Meta_reduce_visit___spec__8(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_ReaderT_bind___at_Lean_Meta_reduce_visit___spec__2___at_Lean_Meta_reduce_visit___spec__9(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___lambda__1(x_1, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Core_withIncRecDepth___at_Lean_Meta_reduce_visit___spec__10___at_Lean_Meta_reduce_visit___spec__11(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Meta_reduce(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_14);
x_16 = l_Lean_Meta_reduce_visit(x_2, x_3, x_4, x_1, x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(lean_object*);
lean_object* initialize_Lean_Util_MonadCache(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Reduce(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
