// Lean compiler output
// Module: Lean.Meta.AbstractNestedProofs
// Imports: Init Lean.Meta.Closure
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxDefinitionFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2;
lean_object* l_Std_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__2(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__1(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1;
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6(lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_AbstractNestedProofs_State_nextIdx___default;
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isAtomic(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_set(x_2, x_3, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = l_Lean_Expr_isAtomic(x_1);
lean_dec(x_1);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_get_size(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_2);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_19, x_19);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_2);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_31 = l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1(x_2, x_29, x_30);
lean_dec(x_2);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
}
}
}
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProof(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Expr_getAppNumArgsAux(x_1, x_19);
x_21 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_20);
x_22 = lean_mk_array(x_20, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_20, x_23);
lean_dec(x_20);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2(x_1, x_22, x_24, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_isNonTrivialProof___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_AbstractNestedProofs_State_nextIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
lean_object* l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_18, x_1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proof");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2;
x_16 = l_Lean_Name_append(x_2, x_15);
x_17 = l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_8, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_23, x_25);
lean_dec(x_23);
x_27 = lean_st_ref_set(x_4, x_26, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Meta_mkAuxDefinitionFor(x_18, x_1, x_5, x_6, x_7, x_8, x_28);
return x_29;
}
}
lean_object* l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkAuxName___at___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_7, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_2, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_4, x_20, x_21, x_22, x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_5(x_3, x_26, x_27, x_28, x_29, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_5, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_6, x_38, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_apply_1(x_8, x_1);
return x_44;
}
}
}
}
lean_object* l_Lean_Meta_AbstractNestedProofs_visit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractNestedProofs_visit_match__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_AbstractNestedProofs_visit(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_2, x_24);
x_2 = x_23;
x_3 = x_25;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_array_set(x_2, x_3, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_1 = x_12;
x_2 = x_14;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_18 = lean_array_get_size(x_2);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = x_2;
x_21 = lean_box_usize(x_19);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1;
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1___boxed), 11, 3);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_20);
x_24 = x_23;
x_25 = lean_apply_8(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_mkAppN(x_1, x_27);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = l_Lean_mkAppN(x_1, x_29);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___rarg), 10, 0);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_AbstractNestedProofs_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = 1;
x_16 = l_Lean_Meta_mkLambdaFVars(x_1, x_12, x_14, x_15, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = l_Lean_LocalDecl_fvarId(x_3);
lean_inc(x_3);
x_23 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_12, x_22, x_3);
x_24 = l_Lean_LocalDecl_index(x_3);
lean_ctor_set(x_14, 0, x_3);
x_25 = l_Std_PersistentArray_set___rarg(x_13, x_24, x_14);
lean_dec(x_24);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_28 = l_Lean_LocalDecl_fvarId(x_3);
lean_inc(x_3);
x_29 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_12, x_28, x_3);
x_30 = l_Lean_LocalDecl_index(x_3);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_3);
x_32 = l_Std_PersistentArray_set___rarg(x_13, x_30, x_31);
lean_dec(x_30);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_35 = x_14;
} else {
 lean_dec_ref(x_14);
 x_35 = lean_box(0);
}
x_36 = l_Lean_LocalDecl_fvarId(x_3);
lean_inc(x_3);
x_37 = l_Std_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_12, x_36, x_3);
x_38 = l_Lean_LocalDecl_index(x_3);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_3);
x_40 = l_Std_PersistentArray_set___rarg(x_13, x_38, x_39);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_3 < x_2;
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_16);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_type(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_AbstractNestedProofs_visit(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_setType(x_18, x_22);
x_25 = l_Lean_LocalDecl_value_x3f(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1(x_16, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = x_3 + x_30;
x_3 = x_31;
x_4 = x_29;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_AbstractNestedProofs_visit(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_LocalDecl_setValue(x_24, x_35);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1(x_16, x_4, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = x_3 + x_42;
x_3 = x_43;
x_4 = x_41;
x_12 = x_40;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_3(x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_1, x_2, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__4), 10, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_3, x_4, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = 1;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_12, x_11, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(x_4, x_16, x_17, x_14, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__7(x_4, x_5, x_19, x_12, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 1;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_AbstractNestedProofs_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_1, x_12, x_14, x_15, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__10), 10, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_3, x_4, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_13, x_12, x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(x_4, x_16, x_17, x_14, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__11(x_4, x_5, x_19, x_12, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_12, x_11, x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_AbstractNestedProofs_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = 1;
x_16 = l_Lean_Meta_mkLambdaFVars(x_1, x_12, x_14, x_15, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_AbstractNestedProofs_visit___spec__3___at_Lean_Meta_AbstractNestedProofs_visit___spec__14), 10, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_3, x_4, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_4);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(x_4, x_16, x_17, x_14, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_withLCtx___at_Lean_Meta_AbstractNestedProofs_visit___spec__6___at_Lean_Meta_AbstractNestedProofs_visit___spec__15(x_4, x_5, x_19, x_12, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 1;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_AbstractNestedProofs_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_24; 
x_24 = l_Lean_Expr_isAtomic(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_st_ref_get(x_8, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_3, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_29, x_1);
lean_dec(x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_free_object(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_32 = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(x_1, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux(x_1, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2(x_1, x_39, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_10 = x_43;
x_11 = x_44;
goto block_23;
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 6:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_50 = l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_10 = x_51;
x_11 = x_52;
goto block_23;
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_58 = l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_10 = x_59;
x_11 = x_60;
goto block_23;
}
else
{
uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 8:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_66 = l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_10 = x_67;
x_11 = x_68;
goto block_23;
}
else
{
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 10:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
lean_dec(x_32);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_75);
x_77 = l_Lean_Meta_AbstractNestedProofs_visit(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set_uint64(x_80, sizeof(void*)*2, x_76);
x_81 = lean_expr_update_mdata(x_80, x_78);
x_10 = x_81;
x_11 = x_79;
goto block_23;
}
else
{
uint8_t x_82; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
case 11:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_32, 1);
lean_inc(x_86);
lean_dec(x_32);
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_89);
x_91 = l_Lean_Meta_AbstractNestedProofs_visit(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_88);
lean_ctor_set(x_94, 2, x_89);
lean_ctor_set_uint64(x_94, sizeof(void*)*3, x_90);
x_95 = lean_expr_update_proj(x_94, x_92);
x_10 = x_95;
x_11 = x_93;
goto block_23;
}
else
{
uint8_t x_96; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
default: 
{
lean_object* x_100; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_100 = lean_ctor_get(x_32, 1);
lean_inc(x_100);
lean_dec(x_32);
lean_inc(x_1);
x_10 = x_1;
x_11 = x_100;
goto block_23;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_32, 1);
lean_inc(x_101);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_1);
x_102 = l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_10 = x_103;
x_11 = x_104;
goto block_23;
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 0);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_102);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_32);
if (x_109 == 0)
{
return x_32;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_32, 0);
x_111 = lean_ctor_get(x_32, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_32);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_31, 0);
lean_inc(x_113);
lean_dec(x_31);
lean_ctor_set(x_27, 0, x_113);
return x_27;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_27, 0);
x_115 = lean_ctor_get(x_27, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_27);
x_116 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_114, x_1);
lean_dec(x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_Lean_Meta_AbstractNestedProofs_isNonTrivialProof(x_1, x_5, x_6, x_7, x_8, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Lean_Expr_getAppNumArgsAux(x_1, x_121);
x_123 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_122);
x_124 = lean_mk_array(x_122, x_123);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_sub(x_122, x_125);
lean_dec(x_122);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_127 = l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2(x_1, x_124, x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_120);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_10 = x_128;
x_11 = x_129;
goto block_23;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
case 6:
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_117, 1);
lean_inc(x_134);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_135 = l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_10 = x_136;
x_11 = x_137;
goto block_23;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_140 = x_135;
} else {
 lean_dec_ref(x_135);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
case 7:
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_117, 1);
lean_inc(x_142);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_143 = l_Lean_Meta_forallTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__12___at_Lean_Meta_AbstractNestedProofs_visit___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_10 = x_144;
x_11 = x_145;
goto block_23;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
case 8:
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_117, 1);
lean_inc(x_150);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_151 = l_Lean_Meta_lambdaLetTelescope___at_Lean_Meta_AbstractNestedProofs_visit___spec__8___at_Lean_Meta_AbstractNestedProofs_visit___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_10 = x_152;
x_11 = x_153;
goto block_23;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
case 10:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint64_t x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
lean_dec(x_117);
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_160);
x_162 = l_Lean_Meta_AbstractNestedProofs_visit(x_160, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set_uint64(x_165, sizeof(void*)*2, x_161);
x_166 = lean_expr_update_mdata(x_165, x_163);
x_10 = x_166;
x_11 = x_164;
goto block_23;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_169 = x_162;
} else {
 lean_dec_ref(x_162);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
case 11:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint64_t x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_117, 1);
lean_inc(x_171);
lean_dec(x_117);
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_1, 2);
lean_inc(x_174);
x_175 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_174);
x_176 = l_Lean_Meta_AbstractNestedProofs_visit(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_179, 0, x_172);
lean_ctor_set(x_179, 1, x_173);
lean_ctor_set(x_179, 2, x_174);
lean_ctor_set_uint64(x_179, sizeof(void*)*3, x_175);
x_180 = lean_expr_update_proj(x_179, x_177);
x_10 = x_180;
x_11 = x_178;
goto block_23;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
default: 
{
lean_object* x_185; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_185 = lean_ctor_get(x_117, 1);
lean_inc(x_185);
lean_dec(x_117);
lean_inc(x_1);
x_10 = x_1;
x_11 = x_185;
goto block_23;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_117, 1);
lean_inc(x_186);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_1);
x_187 = l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_186);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_10 = x_188;
x_11 = x_189;
goto block_23;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_117, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_117, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_196 = x_117;
} else {
 lean_dec_ref(x_117);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_116, 0);
lean_inc(x_198);
lean_dec(x_116);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_115);
return x_199;
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_9);
return x_200;
}
block_23:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_st_ref_get(x_8, x_11);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_10);
x_17 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_15, x_1, x_10);
x_18 = lean_st_ref_set(x_3, x_17, x_16);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Meta_AbstractNestedProofs_visit___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_AbstractNestedProofs_visit___spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_12);
lean_inc(x_18);
x_20 = l_Lean_Meta_AbstractNestedProofs_visit(x_2, x_1, x_18, x_12, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_6, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_18, x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_6, x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_12, x_28);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Closure(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_AbstractNestedProofs(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_AbstractNestedProofs_State_nextIdx___default = _init_l_Lean_Meta_AbstractNestedProofs_State_nextIdx___default();
lean_mark_persistent(l_Lean_Meta_AbstractNestedProofs_State_nextIdx___default);
l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1 = _init_l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__1);
l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2 = _init_l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AbstractNestedProofs_0__Lean_Meta_AbstractNestedProofs_mkAuxLemma___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_AbstractNestedProofs_visit___spec__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
