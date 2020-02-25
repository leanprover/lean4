// Lean compiler output
// Module: Init.Lean.Meta.Check
// Imports: Init.Lean.Meta.InferType
#include "runtime/lean.h"
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__1;
lean_object* l___private_Init_Lean_Meta_Check_4__checkConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_1__ensureType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
lean_object* l___private_Init_Lean_Meta_Check_6__checkAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_7__regTraceClasses(lean_object*);
lean_object* l_Array_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check___closed__2;
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_6__checkAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect___closed__1;
lean_object* l_Lean_Meta_isTypeCorrect___closed__2;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1;
lean_object* l_Lean_Meta_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_5__checkApp___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_4__checkConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData(lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_5__checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_toArray___rarg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Check_1__ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getLevel(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_getFVarLocalDecl(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_8);
x_9 = l___private_Init_Lean_Meta_Check_1__ensureType(x_8, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_3(x_1, x_8, x_3, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_6, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 4);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_17);
x_19 = l___private_Init_Lean_Meta_Check_1__ensureType(x_17, x_3, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_17);
x_21 = lean_apply_3(x_1, x_17, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_18);
x_23 = l_Lean_Meta_inferType(x_18, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
x_26 = l_Lean_Meta_isExprDefEqAux(x_17, x_24, x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Lean_Expr_fvarId_x21(x_2);
x_39 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_39);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Lean_Expr_fvarId_x21(x_2);
x_48 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_dec(x_26);
x_51 = lean_apply_3(x_1, x_18, x_3, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
return x_26;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_23, 0);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_23);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
return x_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_19, 0);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_19);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_5);
if (x_68 == 0)
{
return x_5;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_5, 0);
x_70 = lean_ctor_get(x_5, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_5);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___rarg(x_7, lean_box(0), lean_box(0), x_6, x_2, x_8);
lean_inc(x_4);
x_10 = lean_apply_2(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_3(x_1, x_3, x_4, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Meta_lambdaTelescope___rarg(x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_getFVarLocalDecl(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_LocalDecl_type(x_6);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_8);
x_9 = l___private_Init_Lean_Meta_Check_1__ensureType(x_8, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_3(x_1, x_8, x_3, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___rarg(x_7, lean_box(0), lean_box(0), x_6, x_2, x_8);
lean_inc(x_4);
x_10 = lean_apply_2(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Init_Lean_Meta_Check_1__ensureType(x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_3(x_1, x_3, x_4, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_3__checkForall___lambda__2), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Meta_forallTelescope___rarg(x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Check_3__checkForall___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_4__checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_List_lengthAux___main___rarg(x_2, x_15);
x_17 = l_Lean_ConstantInfo_lparams(x_14);
lean_dec(x_14);
x_18 = l_List_lengthAux___main___rarg(x_17, x_15);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_4__checkConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Check_4__checkConstant(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_5__checkApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_6 = lean_apply_3(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_3(x_1, x_3, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Lean_Meta_inferType(x_2, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnf(x_11, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_inferType(x_3, x_4, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_4);
x_20 = l_Lean_Meta_isExprDefEqAux(x_16, x_18, x_4, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_20, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_20, 0, x_44);
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
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
lean_dec(x_14);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_13, 1);
x_58 = lean_ctor_get(x_13, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_65);
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_dec(x_13);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_4, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_4, 0);
lean_inc(x_70);
lean_dec(x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_3);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_13);
if (x_75 == 0)
{
return x_13;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_13, 0);
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_13);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_10);
if (x_79 == 0)
{
return x_10;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_10, 0);
x_81 = lean_ctor_get(x_10, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_8);
if (x_83 == 0)
{
return x_8;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_8, 0);
x_85 = lean_ctor_get(x_8, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_8);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_6);
if (x_87 == 0)
{
return x_6;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_6, 0);
x_89 = lean_ctor_get(x_6, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_6);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_5__checkApp___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_2, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_inferType(x_1, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_3);
x_12 = l_Lean_Meta_whnf(x_10, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Meta_inferType(x_2, x_3, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_3);
x_19 = l_Lean_Meta_isExprDefEqAux(x_15, x_17, x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_19, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_16);
if (x_51 == 0)
{
return x_16;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_16, 0);
x_53 = lean_ctor_get(x_16, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_16);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_12, 1);
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_2);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_64);
return x_12;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
lean_dec(x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 0);
lean_inc(x_69);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_78; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
return x_9;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_7);
if (x_82 == 0)
{
return x_7;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_7, 0);
x_84 = lean_ctor_get(x_7, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_7);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_5);
if (x_86 == 0)
{
return x_5;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_5);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_10 = l_Lean_Meta_getFVarLocalDecl(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_13);
x_14 = l___private_Init_Lean_Meta_Check_1__ensureType(x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_3);
x_16 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_13, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 4);
lean_inc(x_31);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_30);
x_32 = l___private_Init_Lean_Meta_Check_1__ensureType(x_30, x_3, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_3);
lean_inc(x_30);
x_34 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_30, x_3, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_3);
lean_inc(x_31);
x_36 = l_Lean_Meta_inferType(x_31, x_3, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_39 = l_Lean_Meta_isExprDefEqAux(x_30, x_37, x_3, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_31);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec(x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_49);
x_51 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_52 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_52);
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 0);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_61 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_9);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
lean_inc(x_3);
x_64 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_31, x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_2, x_66);
lean_dec(x_2);
x_2 = x_67;
x_4 = x_65;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
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
uint8_t x_73; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
return x_36;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_36, 0);
x_79 = lean_ctor_get(x_36, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_36);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_34);
if (x_81 == 0)
{
return x_34;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_34, 0);
x_83 = lean_ctor_get(x_34, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_34);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_32);
if (x_85 == 0)
{
return x_32;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_32, 0);
x_87 = lean_ctor_get(x_32, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_32);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_10);
if (x_89 == 0)
{
return x_10;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_10);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1;
x_5 = l_Lean_Meta_lambdaTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_10 = l_Lean_Meta_getFVarLocalDecl(x_9, x_3, x_4);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_13);
x_14 = l___private_Init_Lean_Meta_Check_1__ensureType(x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_3);
x_16 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_13, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Meta_Check_1__ensureType(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_2, x_3, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1;
x_5 = l_Lean_Meta_forallTelescope___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_6__checkAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Init_Lean_Meta_Check_4__checkConstant(x_4, x_5, x_2, x_3);
lean_dec(x_2);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Init_Lean_Meta_Check_5__checkApp___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__1(x_7, x_8, x_2, x_3);
return x_9;
}
case 6:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1___boxed), 4, 0);
x_11 = l_Lean_Meta_lambdaTelescope___rarg(x_1, x_10, x_2, x_3);
return x_11;
}
case 7:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1___boxed), 4, 0);
x_13 = l_Lean_Meta_forallTelescope___rarg(x_1, x_12, x_2, x_3);
return x_13;
}
case 8:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1___boxed), 4, 0);
x_15 = l_Lean_Meta_lambdaTelescope___rarg(x_1, x_14, x_2, x_3);
return x_15;
}
case 10:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_1 = x_16;
goto _start;
}
case 11:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_1 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_6__checkAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; uint16_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_PersistentArray_empty___closed__3;
x_7 = 0;
x_8 = 0;
x_9 = 0;
lean_ctor_set(x_3, 0, x_6);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_7);
lean_ctor_set_uint16(x_3, sizeof(void*)*1 + 4, x_8);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 7, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint16_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_PersistentArray_empty___closed__3;
x_14 = 0;
x_15 = 0;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 6, x_11);
lean_ctor_set_uint32(x_17, sizeof(void*)*1, x_14);
lean_ctor_set_uint16(x_17, sizeof(void*)*1 + 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 7, x_16);
lean_ctor_set(x_1, 4, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_1, 5);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_25 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 6);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
x_28 = l_PersistentArray_empty___closed__3;
x_29 = 0;
x_30 = 0;
x_31 = 0;
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 1, 8);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 6, x_25);
lean_ctor_set_uint32(x_32, sizeof(void*)*1, x_29);
lean_ctor_set_uint16(x_32, sizeof(void*)*1 + 4, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 7, x_31);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint16_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_PersistentArray_toArray___rarg(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_PersistentArray_push___rarg(x_1, x_11);
x_13 = 0;
x_14 = 0;
x_15 = 0;
lean_ctor_set(x_6, 0, x_12);
lean_ctor_set_uint32(x_6, sizeof(void*)*1, x_13);
lean_ctor_set_uint16(x_6, sizeof(void*)*1 + 4, x_14);
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 7, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint16_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_PersistentArray_toArray___rarg(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_PersistentArray_push___rarg(x_1, x_22);
x_24 = 0;
x_25 = 0;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 6, x_18);
lean_ctor_set_uint32(x_27, sizeof(void*)*1, x_24);
lean_ctor_set_uint16(x_27, sizeof(void*)*1 + 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 7, x_26);
lean_ctor_set(x_4, 4, x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint16_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_30 = lean_ctor_get(x_4, 4);
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
x_33 = lean_ctor_get(x_4, 2);
x_34 = lean_ctor_get(x_4, 3);
x_35 = lean_ctor_get(x_4, 5);
lean_inc(x_35);
lean_inc(x_30);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_36 = lean_ctor_get_uint8(x_30, sizeof(void*)*1 + 6);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = l_PersistentArray_toArray___rarg(x_37);
lean_dec(x_37);
x_40 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_PersistentArray_push___rarg(x_1, x_41);
x_43 = 0;
x_44 = 0;
x_45 = 0;
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(0, 1, 8);
} else {
 x_46 = x_38;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 6, x_36);
lean_ctor_set_uint32(x_46, sizeof(void*)*1, x_43);
lean_ctor_set_uint16(x_46, sizeof(void*)*1 + 4, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 7, x_45);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_32);
lean_ctor_set(x_47, 2, x_33);
lean_ctor_set(x_47, 3, x_34);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_35);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Lean_checkTraceOption(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_check___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_check(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_393; uint8_t x_394; 
x_393 = lean_ctor_get(x_3, 4);
lean_inc(x_393);
x_394 = lean_ctor_get_uint8(x_393, sizeof(void*)*1 + 6);
lean_dec(x_393);
if (x_394 == 0)
{
uint8_t x_395; 
x_395 = 0;
x_4 = x_395;
x_5 = x_3;
goto block_392;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_396 = l_Lean_Meta_check___closed__2;
x_397 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_396, x_2, x_3);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_unbox(x_398);
lean_dec(x_398);
x_4 = x_400;
x_5 = x_399;
goto block_392;
}
block_392:
{
if (x_4 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; uint32_t x_11; uint16_t x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 6);
x_10 = 0;
x_11 = 0;
x_12 = 0;
x_13 = 0;
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 6, x_10);
lean_ctor_set_uint32(x_7, sizeof(void*)*1, x_11);
lean_ctor_set_uint16(x_7, sizeof(void*)*1 + 4, x_12);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 7, x_13);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = 0;
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 6, x_17);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 7, x_18);
x_19 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 4);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
uint32_t x_27; uint16_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = 0;
x_29 = 0;
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_21, sizeof(void*)*1, x_27);
lean_ctor_set_uint16(x_21, sizeof(void*)*1 + 4, x_28);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 7, x_29);
return x_19;
}
else
{
lean_object* x_30; uint32_t x_31; uint16_t x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = 0;
x_32 = 0;
x_33 = 0;
x_34 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_34, sizeof(void*)*1, x_31);
lean_ctor_set_uint16(x_34, sizeof(void*)*1 + 4, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 7, x_33);
lean_ctor_set(x_20, 4, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint32_t x_42; uint16_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
x_37 = lean_ctor_get(x_20, 2);
x_38 = lean_ctor_get(x_20, 3);
x_39 = lean_ctor_get(x_20, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_41 = x_21;
} else {
 lean_dec_ref(x_21);
 x_41 = lean_box(0);
}
x_42 = 0;
x_43 = 0;
x_44 = 0;
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 1, 8);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_45, sizeof(void*)*1, x_42);
lean_ctor_set_uint16(x_45, sizeof(void*)*1 + 4, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 7, x_44);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 3, x_38);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_39);
lean_ctor_set(x_19, 1, x_46);
return x_19;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint32_t x_56; uint16_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
lean_dec(x_19);
x_48 = lean_ctor_get(x_20, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_20, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_20, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_20, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 x_53 = x_20;
} else {
 lean_dec_ref(x_20);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_21, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_55 = x_21;
} else {
 lean_dec_ref(x_21);
 x_55 = lean_box(0);
}
x_56 = 0;
x_57 = 0;
x_58 = 0;
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 1, 8);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_59, sizeof(void*)*1, x_56);
lean_ctor_set_uint16(x_59, sizeof(void*)*1 + 4, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 7, x_58);
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_53;
}
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_60, 2, x_50);
lean_ctor_set(x_60, 3, x_51);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_52);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 4);
lean_inc(x_63);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_19, 1);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_62, 4);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
uint32_t x_69; uint16_t x_70; uint8_t x_71; 
x_69 = 0;
x_70 = 0;
x_71 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_63, sizeof(void*)*1, x_69);
lean_ctor_set_uint16(x_63, sizeof(void*)*1 + 4, x_70);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 7, x_71);
return x_19;
}
else
{
lean_object* x_72; uint32_t x_73; uint16_t x_74; uint8_t x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = 0;
x_74 = 0;
x_75 = 0;
x_76 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_76, sizeof(void*)*1, x_73);
lean_ctor_set_uint16(x_76, sizeof(void*)*1 + 4, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1 + 7, x_75);
lean_ctor_set(x_62, 4, x_76);
return x_19;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_62, 0);
x_78 = lean_ctor_get(x_62, 1);
x_79 = lean_ctor_get(x_62, 2);
x_80 = lean_ctor_get(x_62, 3);
x_81 = lean_ctor_get(x_62, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_62);
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_83 = x_63;
} else {
 lean_dec_ref(x_63);
 x_83 = lean_box(0);
}
x_84 = 0;
x_85 = 0;
x_86 = 0;
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set_uint8(x_87, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_87, sizeof(void*)*1, x_84);
lean_ctor_set_uint16(x_87, sizeof(void*)*1 + 4, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1 + 7, x_86);
x_88 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_78);
lean_ctor_set(x_88, 2, x_79);
lean_ctor_set(x_88, 3, x_80);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_81);
lean_ctor_set(x_19, 1, x_88);
return x_19;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; uint16_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_89 = lean_ctor_get(x_19, 0);
lean_inc(x_89);
lean_dec(x_19);
x_90 = lean_ctor_get(x_62, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_62, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_62, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_62, 5);
lean_inc(x_94);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 x_95 = x_62;
} else {
 lean_dec_ref(x_62);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_63, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_97 = x_63;
} else {
 lean_dec_ref(x_63);
 x_97 = lean_box(0);
}
x_98 = 0;
x_99 = 0;
x_100 = 0;
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 1, 8);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_101, sizeof(void*)*1, x_98);
lean_ctor_set_uint16(x_101, sizeof(void*)*1 + 4, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1 + 7, x_100);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 6, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_90);
lean_ctor_set(x_102, 1, x_91);
lean_ctor_set(x_102, 2, x_92);
lean_ctor_set(x_102, 3, x_93);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_94);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_15, 0);
x_105 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_106 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
x_107 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 2);
x_108 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 3);
x_109 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 4);
x_110 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 5);
lean_inc(x_104);
lean_dec(x_15);
x_111 = 0;
x_112 = 0;
x_113 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_105);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 1, x_106);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 2, x_107);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 4, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 5, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 6, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1 + 7, x_112);
lean_ctor_set(x_2, 0, x_113);
x_114 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_5);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; uint16_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_126 = x_116;
} else {
 lean_dec_ref(x_116);
 x_126 = lean_box(0);
}
x_127 = 0;
x_128 = 0;
x_129 = 0;
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 1, 8);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set_uint8(x_130, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_130, sizeof(void*)*1, x_127);
lean_ctor_set_uint16(x_130, sizeof(void*)*1 + 4, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*1 + 7, x_129);
if (lean_is_scalar(x_124)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_124;
}
lean_ctor_set(x_131, 0, x_119);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set(x_131, 2, x_121);
lean_ctor_set(x_131, 3, x_122);
lean_ctor_set(x_131, 4, x_130);
lean_ctor_set(x_131, 5, x_123);
if (lean_is_scalar(x_118)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_118;
}
lean_ctor_set(x_132, 0, x_117);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint32_t x_145; uint16_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_133 = lean_ctor_get(x_114, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_114, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_136 = x_114;
} else {
 lean_dec_ref(x_114);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 x_142 = x_133;
} else {
 lean_dec_ref(x_133);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_144 = x_134;
} else {
 lean_dec_ref(x_134);
 x_144 = lean_box(0);
}
x_145 = 0;
x_146 = 0;
x_147 = 0;
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(0, 1, 8);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set_uint8(x_148, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_148, sizeof(void*)*1, x_145);
lean_ctor_set_uint16(x_148, sizeof(void*)*1 + 4, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1 + 7, x_147);
if (lean_is_scalar(x_142)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_142;
}
lean_ctor_set(x_149, 0, x_137);
lean_ctor_set(x_149, 1, x_138);
lean_ctor_set(x_149, 2, x_139);
lean_ctor_set(x_149, 3, x_140);
lean_ctor_set(x_149, 4, x_148);
lean_ctor_set(x_149, 5, x_141);
if (lean_is_scalar(x_136)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_136;
}
lean_ctor_set(x_150, 0, x_135);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_151 = lean_ctor_get(x_2, 0);
x_152 = lean_ctor_get(x_2, 1);
x_153 = lean_ctor_get(x_2, 2);
x_154 = lean_ctor_get(x_2, 3);
x_155 = lean_ctor_get(x_2, 4);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_2);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
x_157 = lean_ctor_get_uint8(x_151, sizeof(void*)*1);
x_158 = lean_ctor_get_uint8(x_151, sizeof(void*)*1 + 1);
x_159 = lean_ctor_get_uint8(x_151, sizeof(void*)*1 + 2);
x_160 = lean_ctor_get_uint8(x_151, sizeof(void*)*1 + 3);
x_161 = lean_ctor_get_uint8(x_151, sizeof(void*)*1 + 4);
x_162 = lean_ctor_get_uint8(x_151, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_163 = x_151;
} else {
 lean_dec_ref(x_151);
 x_163 = lean_box(0);
}
x_164 = 0;
x_165 = 0;
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(0, 1, 8);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_157);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 1, x_158);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 2, x_159);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 3, x_160);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 4, x_161);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 5, x_162);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 6, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1 + 7, x_165);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_152);
lean_ctor_set(x_167, 2, x_153);
lean_ctor_set(x_167, 3, x_154);
lean_ctor_set(x_167, 4, x_155);
x_168 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_167, x_5);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint32_t x_181; uint16_t x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_172 = x_168;
} else {
 lean_dec_ref(x_168);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 3);
lean_inc(x_176);
x_177 = lean_ctor_get(x_169, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 x_178 = x_169;
} else {
 lean_dec_ref(x_169);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_180 = x_170;
} else {
 lean_dec_ref(x_170);
 x_180 = lean_box(0);
}
x_181 = 0;
x_182 = 0;
x_183 = 0;
if (lean_is_scalar(x_180)) {
 x_184 = lean_alloc_ctor(0, 1, 8);
} else {
 x_184 = x_180;
}
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set_uint8(x_184, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_184, sizeof(void*)*1, x_181);
lean_ctor_set_uint16(x_184, sizeof(void*)*1 + 4, x_182);
lean_ctor_set_uint8(x_184, sizeof(void*)*1 + 7, x_183);
if (lean_is_scalar(x_178)) {
 x_185 = lean_alloc_ctor(0, 6, 0);
} else {
 x_185 = x_178;
}
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_174);
lean_ctor_set(x_185, 2, x_175);
lean_ctor_set(x_185, 3, x_176);
lean_ctor_set(x_185, 4, x_184);
lean_ctor_set(x_185, 5, x_177);
if (lean_is_scalar(x_172)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_172;
}
lean_ctor_set(x_186, 0, x_171);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint32_t x_199; uint16_t x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_168, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_190 = x_168;
} else {
 lean_dec_ref(x_168);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_187, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_187, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 lean_ctor_release(x_187, 5);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_198 = x_188;
} else {
 lean_dec_ref(x_188);
 x_198 = lean_box(0);
}
x_199 = 0;
x_200 = 0;
x_201 = 0;
if (lean_is_scalar(x_198)) {
 x_202 = lean_alloc_ctor(0, 1, 8);
} else {
 x_202 = x_198;
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set_uint8(x_202, sizeof(void*)*1 + 6, x_9);
lean_ctor_set_uint32(x_202, sizeof(void*)*1, x_199);
lean_ctor_set_uint16(x_202, sizeof(void*)*1 + 4, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1 + 7, x_201);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_191);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_193);
lean_ctor_set(x_203, 3, x_194);
lean_ctor_set(x_203, 4, x_202);
lean_ctor_set(x_203, 5, x_195);
if (lean_is_scalar(x_190)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_190;
}
lean_ctor_set(x_204, 0, x_189);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; lean_object* x_206; uint8_t x_207; uint32_t x_208; uint16_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_205 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 6);
x_206 = lean_ctor_get(x_7, 0);
lean_inc(x_206);
lean_dec(x_7);
x_207 = 0;
x_208 = 0;
x_209 = 0;
x_210 = 0;
x_211 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_211, 0, x_206);
lean_ctor_set_uint8(x_211, sizeof(void*)*1 + 6, x_207);
lean_ctor_set_uint32(x_211, sizeof(void*)*1, x_208);
lean_ctor_set_uint16(x_211, sizeof(void*)*1 + 4, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1 + 7, x_210);
lean_ctor_set(x_5, 4, x_211);
x_212 = lean_ctor_get(x_2, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_2, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_2, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_2, 4);
lean_inc(x_216);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_217 = x_2;
} else {
 lean_dec_ref(x_2);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_212, 0);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_212, sizeof(void*)*1);
x_220 = lean_ctor_get_uint8(x_212, sizeof(void*)*1 + 1);
x_221 = lean_ctor_get_uint8(x_212, sizeof(void*)*1 + 2);
x_222 = lean_ctor_get_uint8(x_212, sizeof(void*)*1 + 3);
x_223 = lean_ctor_get_uint8(x_212, sizeof(void*)*1 + 4);
x_224 = lean_ctor_get_uint8(x_212, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_225 = x_212;
} else {
 lean_dec_ref(x_212);
 x_225 = lean_box(0);
}
x_226 = 0;
x_227 = 0;
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 1, 8);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_219);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 1, x_220);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 2, x_221);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 3, x_222);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 4, x_223);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 5, x_224);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 6, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1 + 7, x_227);
if (lean_is_scalar(x_217)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_217;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_213);
lean_ctor_set(x_229, 2, x_214);
lean_ctor_set(x_229, 3, x_215);
lean_ctor_set(x_229, 4, x_216);
x_230 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_229, x_5);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint32_t x_243; uint16_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_231, 3);
lean_inc(x_238);
x_239 = lean_ctor_get(x_231, 5);
lean_inc(x_239);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 lean_ctor_release(x_231, 3);
 lean_ctor_release(x_231, 4);
 lean_ctor_release(x_231, 5);
 x_240 = x_231;
} else {
 lean_dec_ref(x_231);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_232, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_242 = x_232;
} else {
 lean_dec_ref(x_232);
 x_242 = lean_box(0);
}
x_243 = 0;
x_244 = 0;
x_245 = 0;
if (lean_is_scalar(x_242)) {
 x_246 = lean_alloc_ctor(0, 1, 8);
} else {
 x_246 = x_242;
}
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set_uint8(x_246, sizeof(void*)*1 + 6, x_205);
lean_ctor_set_uint32(x_246, sizeof(void*)*1, x_243);
lean_ctor_set_uint16(x_246, sizeof(void*)*1 + 4, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*1 + 7, x_245);
if (lean_is_scalar(x_240)) {
 x_247 = lean_alloc_ctor(0, 6, 0);
} else {
 x_247 = x_240;
}
lean_ctor_set(x_247, 0, x_235);
lean_ctor_set(x_247, 1, x_236);
lean_ctor_set(x_247, 2, x_237);
lean_ctor_set(x_247, 3, x_238);
lean_ctor_set(x_247, 4, x_246);
lean_ctor_set(x_247, 5, x_239);
if (lean_is_scalar(x_234)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_234;
}
lean_ctor_set(x_248, 0, x_233);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint32_t x_261; uint16_t x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_249 = lean_ctor_get(x_230, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 4);
lean_inc(x_250);
x_251 = lean_ctor_get(x_230, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_252 = x_230;
} else {
 lean_dec_ref(x_230);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_249, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_249, 5);
lean_inc(x_257);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 lean_ctor_release(x_249, 4);
 lean_ctor_release(x_249, 5);
 x_258 = x_249;
} else {
 lean_dec_ref(x_249);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_250, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_260 = x_250;
} else {
 lean_dec_ref(x_250);
 x_260 = lean_box(0);
}
x_261 = 0;
x_262 = 0;
x_263 = 0;
if (lean_is_scalar(x_260)) {
 x_264 = lean_alloc_ctor(0, 1, 8);
} else {
 x_264 = x_260;
}
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set_uint8(x_264, sizeof(void*)*1 + 6, x_205);
lean_ctor_set_uint32(x_264, sizeof(void*)*1, x_261);
lean_ctor_set_uint16(x_264, sizeof(void*)*1 + 4, x_262);
lean_ctor_set_uint8(x_264, sizeof(void*)*1 + 7, x_263);
if (lean_is_scalar(x_258)) {
 x_265 = lean_alloc_ctor(0, 6, 0);
} else {
 x_265 = x_258;
}
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_256);
lean_ctor_set(x_265, 4, x_264);
lean_ctor_set(x_265, 5, x_257);
if (lean_is_scalar(x_252)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_252;
}
lean_ctor_set(x_266, 0, x_251);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; uint32_t x_277; uint16_t x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_267 = lean_ctor_get(x_5, 4);
x_268 = lean_ctor_get(x_5, 0);
x_269 = lean_ctor_get(x_5, 1);
x_270 = lean_ctor_get(x_5, 2);
x_271 = lean_ctor_get(x_5, 3);
x_272 = lean_ctor_get(x_5, 5);
lean_inc(x_272);
lean_inc(x_267);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_5);
x_273 = lean_ctor_get_uint8(x_267, sizeof(void*)*1 + 6);
x_274 = lean_ctor_get(x_267, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_275 = x_267;
} else {
 lean_dec_ref(x_267);
 x_275 = lean_box(0);
}
x_276 = 0;
x_277 = 0;
x_278 = 0;
x_279 = 0;
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 1, 8);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_274);
lean_ctor_set_uint8(x_280, sizeof(void*)*1 + 6, x_276);
lean_ctor_set_uint32(x_280, sizeof(void*)*1, x_277);
lean_ctor_set_uint16(x_280, sizeof(void*)*1 + 4, x_278);
lean_ctor_set_uint8(x_280, sizeof(void*)*1 + 7, x_279);
x_281 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_281, 0, x_268);
lean_ctor_set(x_281, 1, x_269);
lean_ctor_set(x_281, 2, x_270);
lean_ctor_set(x_281, 3, x_271);
lean_ctor_set(x_281, 4, x_280);
lean_ctor_set(x_281, 5, x_272);
x_282 = lean_ctor_get(x_2, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_2, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_2, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_2, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_2, 4);
lean_inc(x_286);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_287 = x_2;
} else {
 lean_dec_ref(x_2);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_282, 0);
lean_inc(x_288);
x_289 = lean_ctor_get_uint8(x_282, sizeof(void*)*1);
x_290 = lean_ctor_get_uint8(x_282, sizeof(void*)*1 + 1);
x_291 = lean_ctor_get_uint8(x_282, sizeof(void*)*1 + 2);
x_292 = lean_ctor_get_uint8(x_282, sizeof(void*)*1 + 3);
x_293 = lean_ctor_get_uint8(x_282, sizeof(void*)*1 + 4);
x_294 = lean_ctor_get_uint8(x_282, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_295 = x_282;
} else {
 lean_dec_ref(x_282);
 x_295 = lean_box(0);
}
x_296 = 0;
x_297 = 0;
if (lean_is_scalar(x_295)) {
 x_298 = lean_alloc_ctor(0, 1, 8);
} else {
 x_298 = x_295;
}
lean_ctor_set(x_298, 0, x_288);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_289);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 1, x_290);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 2, x_291);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 3, x_292);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 4, x_293);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 5, x_294);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 6, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*1 + 7, x_297);
if (lean_is_scalar(x_287)) {
 x_299 = lean_alloc_ctor(0, 5, 0);
} else {
 x_299 = x_287;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_283);
lean_ctor_set(x_299, 2, x_284);
lean_ctor_set(x_299, 3, x_285);
lean_ctor_set(x_299, 4, x_286);
x_300 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_299, x_281);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint32_t x_313; uint16_t x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_301, 4);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_304 = x_300;
} else {
 lean_dec_ref(x_300);
 x_304 = lean_box(0);
}
x_305 = lean_ctor_get(x_301, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_301, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_301, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_301, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_301, 5);
lean_inc(x_309);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 lean_ctor_release(x_301, 4);
 lean_ctor_release(x_301, 5);
 x_310 = x_301;
} else {
 lean_dec_ref(x_301);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_302, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_312 = x_302;
} else {
 lean_dec_ref(x_302);
 x_312 = lean_box(0);
}
x_313 = 0;
x_314 = 0;
x_315 = 0;
if (lean_is_scalar(x_312)) {
 x_316 = lean_alloc_ctor(0, 1, 8);
} else {
 x_316 = x_312;
}
lean_ctor_set(x_316, 0, x_311);
lean_ctor_set_uint8(x_316, sizeof(void*)*1 + 6, x_273);
lean_ctor_set_uint32(x_316, sizeof(void*)*1, x_313);
lean_ctor_set_uint16(x_316, sizeof(void*)*1 + 4, x_314);
lean_ctor_set_uint8(x_316, sizeof(void*)*1 + 7, x_315);
if (lean_is_scalar(x_310)) {
 x_317 = lean_alloc_ctor(0, 6, 0);
} else {
 x_317 = x_310;
}
lean_ctor_set(x_317, 0, x_305);
lean_ctor_set(x_317, 1, x_306);
lean_ctor_set(x_317, 2, x_307);
lean_ctor_set(x_317, 3, x_308);
lean_ctor_set(x_317, 4, x_316);
lean_ctor_set(x_317, 5, x_309);
if (lean_is_scalar(x_304)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_304;
}
lean_ctor_set(x_318, 0, x_303);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_319 = lean_ctor_get(x_300, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_319, 4);
lean_inc(x_320);
x_321 = lean_ctor_get(x_300, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_322 = x_300;
} else {
 lean_dec_ref(x_300);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_319, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_319, 5);
lean_inc(x_327);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 lean_ctor_release(x_319, 3);
 lean_ctor_release(x_319, 4);
 lean_ctor_release(x_319, 5);
 x_328 = x_319;
} else {
 lean_dec_ref(x_319);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_320, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 x_330 = x_320;
} else {
 lean_dec_ref(x_320);
 x_330 = lean_box(0);
}
x_331 = 0;
x_332 = 0;
x_333 = 0;
if (lean_is_scalar(x_330)) {
 x_334 = lean_alloc_ctor(0, 1, 8);
} else {
 x_334 = x_330;
}
lean_ctor_set(x_334, 0, x_329);
lean_ctor_set_uint8(x_334, sizeof(void*)*1 + 6, x_273);
lean_ctor_set_uint32(x_334, sizeof(void*)*1, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*1 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*1 + 7, x_333);
if (lean_is_scalar(x_328)) {
 x_335 = lean_alloc_ctor(0, 6, 0);
} else {
 x_335 = x_328;
}
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_324);
lean_ctor_set(x_335, 2, x_325);
lean_ctor_set(x_335, 3, x_326);
lean_ctor_set(x_335, 4, x_334);
lean_ctor_set(x_335, 5, x_327);
if (lean_is_scalar(x_322)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_322;
}
lean_ctor_set(x_336, 0, x_321);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_337 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_5);
x_338 = lean_ctor_get(x_2, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_341 = lean_ctor_get(x_2, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_2, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_2, 3);
lean_inc(x_343);
x_344 = lean_ctor_get(x_2, 4);
lean_inc(x_344);
x_345 = !lean_is_exclusive(x_338);
if (x_345 == 0)
{
uint8_t x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_346 = 0;
x_347 = 0;
lean_ctor_set_uint8(x_338, sizeof(void*)*1 + 6, x_346);
lean_ctor_set_uint8(x_338, sizeof(void*)*1 + 7, x_347);
x_348 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_341);
lean_ctor_set(x_348, 2, x_342);
lean_ctor_set(x_348, 3, x_343);
lean_ctor_set(x_348, 4, x_344);
x_349 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_348, x_340);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = l_Lean_Meta_check___closed__2;
x_353 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_339, x_352, x_2, x_351);
lean_dec(x_2);
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 0);
lean_dec(x_355);
lean_ctor_set(x_353, 0, x_350);
return x_353;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
lean_dec(x_353);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_350);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_358 = lean_ctor_get(x_349, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_349, 1);
lean_inc(x_359);
lean_dec(x_349);
x_360 = l_Lean_Meta_check___closed__2;
x_361 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_339, x_360, x_2, x_359);
lean_dec(x_2);
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_361, 0);
lean_dec(x_363);
lean_ctor_set_tag(x_361, 1);
lean_ctor_set(x_361, 0, x_358);
return x_361;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_361, 1);
lean_inc(x_364);
lean_dec(x_361);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_358);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_366 = lean_ctor_get(x_338, 0);
x_367 = lean_ctor_get_uint8(x_338, sizeof(void*)*1);
x_368 = lean_ctor_get_uint8(x_338, sizeof(void*)*1 + 1);
x_369 = lean_ctor_get_uint8(x_338, sizeof(void*)*1 + 2);
x_370 = lean_ctor_get_uint8(x_338, sizeof(void*)*1 + 3);
x_371 = lean_ctor_get_uint8(x_338, sizeof(void*)*1 + 4);
x_372 = lean_ctor_get_uint8(x_338, sizeof(void*)*1 + 5);
lean_inc(x_366);
lean_dec(x_338);
x_373 = 0;
x_374 = 0;
x_375 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_375, 0, x_366);
lean_ctor_set_uint8(x_375, sizeof(void*)*1, x_367);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 1, x_368);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 2, x_369);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 3, x_370);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 4, x_371);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 5, x_372);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 6, x_373);
lean_ctor_set_uint8(x_375, sizeof(void*)*1 + 7, x_374);
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_341);
lean_ctor_set(x_376, 2, x_342);
lean_ctor_set(x_376, 3, x_343);
lean_ctor_set(x_376, 4, x_344);
x_377 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_376, x_340);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = l_Lean_Meta_check___closed__2;
x_381 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_339, x_380, x_2, x_379);
lean_dec(x_2);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_378);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_385 = lean_ctor_get(x_377, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_377, 1);
lean_inc(x_386);
lean_dec(x_377);
x_387 = l_Lean_Meta_check___closed__2;
x_388 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_339, x_387, x_2, x_386);
lean_dec(x_2);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_390 = x_388;
} else {
 lean_dec_ref(x_388);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
 lean_ctor_set_tag(x_391, 1);
}
lean_ctor_set(x_391, 0, x_385);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Meta_addContext(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 4);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint16_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_PersistentArray_push___rarg(x_14, x_15);
x_17 = 0;
x_18 = 0;
x_19 = 0;
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set_uint32(x_7, sizeof(void*)*1, x_17);
lean_ctor_set_uint16(x_7, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 7, x_19);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 6);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_9);
x_24 = l_PersistentArray_push___rarg(x_22, x_23);
x_25 = 0;
x_26 = 0;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 6, x_21);
lean_ctor_set_uint32(x_28, sizeof(void*)*1, x_25);
lean_ctor_set_uint16(x_28, sizeof(void*)*1 + 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 7, x_27);
lean_ctor_set(x_6, 4, x_28);
x_29 = lean_box(0);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_35 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 6);
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_37 = x_7;
} else {
 lean_dec_ref(x_7);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_9);
x_39 = l_PersistentArray_push___rarg(x_36, x_38);
x_40 = 0;
x_41 = 0;
x_42 = 0;
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 1, 8);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 6, x_35);
lean_ctor_set_uint32(x_43, sizeof(void*)*1, x_40);
lean_ctor_set_uint16(x_43, sizeof(void*)*1 + 4, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 7, x_42);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set(x_44, 3, x_33);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_34);
x_45 = lean_box(0);
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_45);
return x_5;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint32_t x_58; uint16_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_6, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_6, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 5);
lean_inc(x_51);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_52 = x_6;
} else {
 lean_dec_ref(x_6);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 6);
x_54 = lean_ctor_get(x_7, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_55 = x_7;
} else {
 lean_dec_ref(x_7);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_46);
x_57 = l_PersistentArray_push___rarg(x_54, x_56);
x_58 = 0;
x_59 = 0;
x_60 = 0;
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 1, 8);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 6, x_53);
lean_ctor_set_uint32(x_61, sizeof(void*)*1, x_58);
lean_ctor_set_uint16(x_61, sizeof(void*)*1 + 4, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 7, x_60);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_49);
lean_ctor_set(x_62, 3, x_50);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_51);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeError");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_isTypeCorrect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isTypeCorrect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_isTypeCorrect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_35; lean_object* x_36; lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_3, 4);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1 + 6);
lean_dec(x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 0;
x_35 = x_240;
x_36 = x_3;
goto block_237;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = l_Lean_Meta_check___closed__2;
x_242 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_241, x_2, x_3);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_unbox(x_243);
lean_dec(x_243);
x_35 = x_245;
x_36 = x_244;
goto block_237;
}
block_34:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_isTypeCorrect___closed__2;
x_12 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_11, x_2, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = l_Lean_Meta_Exception_toTraceMessageData(x_4);
x_25 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_11, x_24, x_2, x_23);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
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
block_237:
{
if (x_35 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 4);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; uint32_t x_42; uint16_t x_43; uint8_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 6);
x_41 = 0;
x_42 = 0;
x_43 = 0;
x_44 = 0;
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 6, x_41);
lean_ctor_set_uint32(x_38, sizeof(void*)*1, x_42);
lean_ctor_set_uint16(x_38, sizeof(void*)*1 + 4, x_43);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 7, x_44);
lean_inc(x_2);
x_45 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_36);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 4);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
uint32_t x_52; uint16_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_52 = 0;
x_53 = 0;
x_54 = 0;
lean_ctor_set_uint8(x_50, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_50, sizeof(void*)*1, x_52);
lean_ctor_set_uint16(x_50, sizeof(void*)*1 + 4, x_53);
lean_ctor_set_uint8(x_50, sizeof(void*)*1 + 7, x_54);
x_55 = 1;
x_56 = lean_box(x_55);
lean_ctor_set(x_45, 0, x_56);
return x_45;
}
else
{
lean_object* x_57; uint32_t x_58; uint16_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = 0;
x_59 = 0;
x_60 = 0;
x_61 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_61, sizeof(void*)*1, x_58);
lean_ctor_set_uint16(x_61, sizeof(void*)*1 + 4, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 7, x_60);
lean_ctor_set(x_47, 4, x_61);
x_62 = 1;
x_63 = lean_box(x_62);
lean_ctor_set(x_45, 0, x_63);
return x_45;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint32_t x_72; uint16_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_47, 4);
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = lean_ctor_get(x_47, 5);
lean_inc(x_69);
lean_inc(x_64);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_47);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
x_72 = 0;
x_73 = 0;
x_74 = 0;
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 1, 8);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_75, sizeof(void*)*1, x_72);
lean_ctor_set_uint16(x_75, sizeof(void*)*1 + 4, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 7, x_74);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_76, 2, x_67);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_69);
x_77 = 1;
x_78 = lean_box(x_77);
lean_ctor_set(x_45, 1, x_76);
lean_ctor_set(x_45, 0, x_78);
return x_45;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint32_t x_89; uint16_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_79 = lean_ctor_get(x_45, 1);
lean_inc(x_79);
lean_dec(x_45);
x_80 = lean_ctor_get(x_79, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
x_89 = 0;
x_90 = 0;
x_91 = 0;
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 1, 8);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set_uint8(x_92, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_92, sizeof(void*)*1, x_89);
lean_ctor_set_uint16(x_92, sizeof(void*)*1 + 4, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1 + 7, x_91);
if (lean_is_scalar(x_86)) {
 x_93 = lean_alloc_ctor(0, 6, 0);
} else {
 x_93 = x_86;
}
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_82);
lean_ctor_set(x_93, 2, x_83);
lean_ctor_set(x_93, 3, x_84);
lean_ctor_set(x_93, 4, x_92);
lean_ctor_set(x_93, 5, x_85);
x_94 = 1;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_45, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_45, 0);
lean_inc(x_99);
lean_dec(x_45);
x_100 = !lean_is_exclusive(x_97);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_97, 4);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
uint32_t x_103; uint16_t x_104; uint8_t x_105; 
x_103 = 0;
x_104 = 0;
x_105 = 0;
lean_ctor_set_uint8(x_98, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_98, sizeof(void*)*1, x_103);
lean_ctor_set_uint16(x_98, sizeof(void*)*1 + 4, x_104);
lean_ctor_set_uint8(x_98, sizeof(void*)*1 + 7, x_105);
x_4 = x_99;
x_5 = x_97;
goto block_34;
}
else
{
lean_object* x_106; uint32_t x_107; uint16_t x_108; uint8_t x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
lean_dec(x_98);
x_107 = 0;
x_108 = 0;
x_109 = 0;
x_110 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_110, sizeof(void*)*1, x_107);
lean_ctor_set_uint16(x_110, sizeof(void*)*1 + 4, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1 + 7, x_109);
lean_ctor_set(x_97, 4, x_110);
x_4 = x_99;
x_5 = x_97;
goto block_34;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint32_t x_118; uint16_t x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_97, 0);
x_112 = lean_ctor_get(x_97, 1);
x_113 = lean_ctor_get(x_97, 2);
x_114 = lean_ctor_get(x_97, 3);
x_115 = lean_ctor_get(x_97, 5);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_97);
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_117 = x_98;
} else {
 lean_dec_ref(x_98);
 x_117 = lean_box(0);
}
x_118 = 0;
x_119 = 0;
x_120 = 0;
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 6, x_40);
lean_ctor_set_uint32(x_121, sizeof(void*)*1, x_118);
lean_ctor_set_uint16(x_121, sizeof(void*)*1 + 4, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1 + 7, x_120);
x_122 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_112);
lean_ctor_set(x_122, 2, x_113);
lean_ctor_set(x_122, 3, x_114);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_115);
x_4 = x_99;
x_5 = x_122;
goto block_34;
}
}
}
else
{
uint8_t x_123; lean_object* x_124; uint8_t x_125; uint32_t x_126; uint16_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 6);
x_124 = lean_ctor_get(x_38, 0);
lean_inc(x_124);
lean_dec(x_38);
x_125 = 0;
x_126 = 0;
x_127 = 0;
x_128 = 0;
x_129 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set_uint8(x_129, sizeof(void*)*1 + 6, x_125);
lean_ctor_set_uint32(x_129, sizeof(void*)*1, x_126);
lean_ctor_set_uint16(x_129, sizeof(void*)*1 + 4, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1 + 7, x_128);
lean_ctor_set(x_36, 4, x_129);
lean_inc(x_2);
x_130 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_36);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint32_t x_142; uint16_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_2);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_131, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_141 = x_133;
} else {
 lean_dec_ref(x_133);
 x_141 = lean_box(0);
}
x_142 = 0;
x_143 = 0;
x_144 = 0;
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(0, 1, 8);
} else {
 x_145 = x_141;
}
lean_ctor_set(x_145, 0, x_140);
lean_ctor_set_uint8(x_145, sizeof(void*)*1 + 6, x_123);
lean_ctor_set_uint32(x_145, sizeof(void*)*1, x_142);
lean_ctor_set_uint16(x_145, sizeof(void*)*1 + 4, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1 + 7, x_144);
if (lean_is_scalar(x_139)) {
 x_146 = lean_alloc_ctor(0, 6, 0);
} else {
 x_146 = x_139;
}
lean_ctor_set(x_146, 0, x_134);
lean_ctor_set(x_146, 1, x_135);
lean_ctor_set(x_146, 2, x_136);
lean_ctor_set(x_146, 3, x_137);
lean_ctor_set(x_146, 4, x_145);
lean_ctor_set(x_146, 5, x_138);
x_147 = 1;
x_148 = lean_box(x_147);
if (lean_is_scalar(x_132)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_132;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint32_t x_161; uint16_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_150 = lean_ctor_get(x_130, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_130, 0);
lean_inc(x_152);
lean_dec(x_130);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 5);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 lean_ctor_release(x_150, 5);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_160 = x_151;
} else {
 lean_dec_ref(x_151);
 x_160 = lean_box(0);
}
x_161 = 0;
x_162 = 0;
x_163 = 0;
if (lean_is_scalar(x_160)) {
 x_164 = lean_alloc_ctor(0, 1, 8);
} else {
 x_164 = x_160;
}
lean_ctor_set(x_164, 0, x_159);
lean_ctor_set_uint8(x_164, sizeof(void*)*1 + 6, x_123);
lean_ctor_set_uint32(x_164, sizeof(void*)*1, x_161);
lean_ctor_set_uint16(x_164, sizeof(void*)*1 + 4, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1 + 7, x_163);
if (lean_is_scalar(x_158)) {
 x_165 = lean_alloc_ctor(0, 6, 0);
} else {
 x_165 = x_158;
}
lean_ctor_set(x_165, 0, x_153);
lean_ctor_set(x_165, 1, x_154);
lean_ctor_set(x_165, 2, x_155);
lean_ctor_set(x_165, 3, x_156);
lean_ctor_set(x_165, 4, x_164);
lean_ctor_set(x_165, 5, x_157);
x_4 = x_152;
x_5 = x_165;
goto block_34;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint32_t x_176; uint16_t x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_166 = lean_ctor_get(x_36, 4);
x_167 = lean_ctor_get(x_36, 0);
x_168 = lean_ctor_get(x_36, 1);
x_169 = lean_ctor_get(x_36, 2);
x_170 = lean_ctor_get(x_36, 3);
x_171 = lean_ctor_get(x_36, 5);
lean_inc(x_171);
lean_inc(x_166);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_36);
x_172 = lean_ctor_get_uint8(x_166, sizeof(void*)*1 + 6);
x_173 = lean_ctor_get(x_166, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_174 = x_166;
} else {
 lean_dec_ref(x_166);
 x_174 = lean_box(0);
}
x_175 = 0;
x_176 = 0;
x_177 = 0;
x_178 = 0;
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 1, 8);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set_uint8(x_179, sizeof(void*)*1 + 6, x_175);
lean_ctor_set_uint32(x_179, sizeof(void*)*1, x_176);
lean_ctor_set_uint16(x_179, sizeof(void*)*1 + 4, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*1 + 7, x_178);
x_180 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_180, 0, x_167);
lean_ctor_set(x_180, 1, x_168);
lean_ctor_set(x_180, 2, x_169);
lean_ctor_set(x_180, 3, x_170);
lean_ctor_set(x_180, 4, x_179);
lean_ctor_set(x_180, 5, x_171);
lean_inc(x_2);
x_181 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint32_t x_193; uint16_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_2);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_182, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_182, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_182, 5);
lean_inc(x_189);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 lean_ctor_release(x_182, 5);
 x_190 = x_182;
} else {
 lean_dec_ref(x_182);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_184, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
 x_192 = lean_box(0);
}
x_193 = 0;
x_194 = 0;
x_195 = 0;
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 1, 8);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set_uint8(x_196, sizeof(void*)*1 + 6, x_172);
lean_ctor_set_uint32(x_196, sizeof(void*)*1, x_193);
lean_ctor_set_uint16(x_196, sizeof(void*)*1 + 4, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1 + 7, x_195);
if (lean_is_scalar(x_190)) {
 x_197 = lean_alloc_ctor(0, 6, 0);
} else {
 x_197 = x_190;
}
lean_ctor_set(x_197, 0, x_185);
lean_ctor_set(x_197, 1, x_186);
lean_ctor_set(x_197, 2, x_187);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set(x_197, 4, x_196);
lean_ctor_set(x_197, 5, x_189);
x_198 = 1;
x_199 = lean_box(x_198);
if (lean_is_scalar(x_183)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_183;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint32_t x_212; uint16_t x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_201 = lean_ctor_get(x_181, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_181, 0);
lean_inc(x_203);
lean_dec(x_181);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 5);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_202, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_211 = x_202;
} else {
 lean_dec_ref(x_202);
 x_211 = lean_box(0);
}
x_212 = 0;
x_213 = 0;
x_214 = 0;
if (lean_is_scalar(x_211)) {
 x_215 = lean_alloc_ctor(0, 1, 8);
} else {
 x_215 = x_211;
}
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set_uint8(x_215, sizeof(void*)*1 + 6, x_172);
lean_ctor_set_uint32(x_215, sizeof(void*)*1, x_212);
lean_ctor_set_uint16(x_215, sizeof(void*)*1 + 4, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*1 + 7, x_214);
if (lean_is_scalar(x_209)) {
 x_216 = lean_alloc_ctor(0, 6, 0);
} else {
 x_216 = x_209;
}
lean_ctor_set(x_216, 0, x_204);
lean_ctor_set(x_216, 1, x_205);
lean_ctor_set(x_216, 2, x_206);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_215);
lean_ctor_set(x_216, 5, x_208);
x_4 = x_203;
x_5 = x_216;
goto block_34;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at_Lean_Meta_check___spec__1___rarg(x_36);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_2);
x_220 = l___private_Init_Lean_Meta_Check_6__checkAux___main(x_1, x_2, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Meta_check___closed__2;
x_223 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_218, x_222, x_2, x_221);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_223, 0);
lean_dec(x_225);
x_226 = 1;
x_227 = lean_box(x_226);
lean_ctor_set(x_223, 0, x_227);
return x_223;
}
else
{
lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_dec(x_223);
x_229 = 1;
x_230 = lean_box(x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_220, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_220, 1);
lean_inc(x_233);
lean_dec(x_220);
x_234 = l_Lean_Meta_check___closed__2;
x_235 = l___private_Init_Lean_Util_Trace_2__addNode___at_Lean_Meta_check___spec__2(x_218, x_234, x_2, x_233);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_4 = x_232;
x_5 = x_236;
goto block_34;
}
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Check_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_check___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_isTypeCorrect___closed__2;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Check(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_InferType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1 = _init_l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Check_2__checkLambdaLet___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__2___closed__1);
l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1 = _init_l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Check_3__checkForall___at___private_Init_Lean_Meta_Check_6__checkAux___main___spec__4___closed__1);
l_Lean_Meta_check___closed__1 = _init_l_Lean_Meta_check___closed__1();
lean_mark_persistent(l_Lean_Meta_check___closed__1);
l_Lean_Meta_check___closed__2 = _init_l_Lean_Meta_check___closed__2();
lean_mark_persistent(l_Lean_Meta_check___closed__2);
l_Lean_Meta_isTypeCorrect___closed__1 = _init_l_Lean_Meta_isTypeCorrect___closed__1();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__1);
l_Lean_Meta_isTypeCorrect___closed__2 = _init_l_Lean_Meta_isTypeCorrect___closed__2();
lean_mark_persistent(l_Lean_Meta_isTypeCorrect___closed__2);
res = l___private_Init_Lean_Meta_Check_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
