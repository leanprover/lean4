// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: Init Lean.Meta.Offset
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
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2;
lean_object* l_Lean_Meta_Nat_hasReduceEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Nat_hasReduceEval___closed__3;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6;
extern lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main(lean_object*);
extern lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Meta_Option_hasReduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_String_hasReduceEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5;
lean_object* l_Lean_Meta_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Name_hasReduceEval___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Nat_hasReduceEval___closed__1;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__1;
extern lean_object* l___private_Lean_Syntax_7__quoteName___main___closed__2;
lean_object* l_Lean_Meta_reduceEval(lean_object*);
lean_object* l_Lean_Meta_Option_hasReduceEval(lean_object*);
lean_object* l_Lean_Meta_Name_hasReduceEval;
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Nat_hasReduceEval___closed__2;
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint8(x_9, 5);
x_12 = 1;
x_13 = l_Lean_Meta_TransparencyMode_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; 
lean_ctor_set_uint8(x_9, 5, x_12);
x_15 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
else
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_16 = lean_ctor_get_uint8(x_9, 0);
x_17 = lean_ctor_get_uint8(x_9, 1);
x_18 = lean_ctor_get_uint8(x_9, 2);
x_19 = lean_ctor_get_uint8(x_9, 3);
x_20 = lean_ctor_get_uint8(x_9, 4);
x_21 = lean_ctor_get_uint8(x_9, 5);
lean_dec(x_9);
x_22 = 1;
x_23 = l_Lean_Meta_TransparencyMode_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_24, 0, x_16);
lean_ctor_set_uint8(x_24, 1, x_17);
lean_ctor_set_uint8(x_24, 2, x_18);
lean_ctor_set_uint8(x_24, 3, x_19);
lean_ctor_set_uint8(x_24, 4, x_20);
lean_ctor_set_uint8(x_24, 5, x_21);
lean_ctor_set(x_3, 0, x_24);
x_25 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_26, 0, x_16);
lean_ctor_set_uint8(x_26, 1, x_17);
lean_ctor_set_uint8(x_26, 2, x_18);
lean_ctor_set_uint8(x_26, 3, x_19);
lean_ctor_set_uint8(x_26, 4, x_20);
lean_ctor_set_uint8(x_26, 5, x_22);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_31 = lean_ctor_get_uint8(x_28, 0);
x_32 = lean_ctor_get_uint8(x_28, 1);
x_33 = lean_ctor_get_uint8(x_28, 2);
x_34 = lean_ctor_get_uint8(x_28, 3);
x_35 = lean_ctor_get_uint8(x_28, 4);
x_36 = lean_ctor_get_uint8(x_28, 5);
if (lean_is_exclusive(x_28)) {
 x_37 = x_28;
} else {
 lean_dec_ref(x_28);
 x_37 = lean_box(0);
}
x_38 = 1;
x_39 = l_Lean_Meta_TransparencyMode_lt(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 0, 6);
} else {
 x_40 = x_37;
}
lean_ctor_set_uint8(x_40, 0, x_31);
lean_ctor_set_uint8(x_40, 1, x_32);
lean_ctor_set_uint8(x_40, 2, x_33);
lean_ctor_set_uint8(x_40, 3, x_34);
lean_ctor_set_uint8(x_40, 4, x_35);
lean_ctor_set_uint8(x_40, 5, x_36);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
x_42 = lean_apply_6(x_1, x_2, x_41, x_4, x_5, x_6, x_7);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 0, 6);
} else {
 x_43 = x_37;
}
lean_ctor_set_uint8(x_43, 0, x_31);
lean_ctor_set_uint8(x_43, 1, x_32);
lean_ctor_set_uint8(x_43, 2, x_33);
lean_ctor_set_uint8(x_43, 3, x_34);
lean_ctor_set_uint8(x_43, 4, x_35);
lean_ctor_set_uint8(x_43, 5, x_38);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
lean_ctor_set(x_44, 2, x_30);
x_45 = lean_apply_6(x_1, x_2, x_44, x_4, x_5, x_6, x_7);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_reduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceEval___rarg), 7, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Nat_hasReduceEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceEval: failed to evaluate argument: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Nat_hasReduceEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Nat_hasReduceEval___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Nat_hasReduceEval___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Nat_hasReduceEval___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Nat_hasReduceEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Meta_evalNat___main(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
x_12 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_throwError___rarg(x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_19);
x_21 = l_Lean_Meta_evalNat___main(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_expr_dbg_to_string(x_19);
lean_dec(x_19);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_throwError___rarg(x_26, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_Option_hasReduceEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_20 = l_Lean_Expr_getAppFn___main(x_10);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_22);
x_24 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
x_25 = lean_name_eq(x_21, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_free_object(x_8);
x_26 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_27 = lean_name_eq(x_21, x_26);
lean_dec(x_21);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_1);
x_28 = lean_box(0);
x_12 = x_28;
goto block_19;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_dec_eq(x_23, x_29);
lean_dec(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_1);
x_31 = lean_box(0);
x_12 = x_31;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_33 = l_Lean_Meta_reduceEval___rarg(x_1, x_32, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_eq(x_23, x_22);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_free_object(x_8);
x_46 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_47 = lean_name_eq(x_21, x_46);
lean_dec(x_21);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_23);
lean_dec(x_1);
x_48 = lean_box(0);
x_12 = x_48;
goto block_19;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_dec_eq(x_23, x_49);
lean_dec(x_23);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = lean_box(0);
x_12 = x_51;
goto block_19;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_53 = l_Lean_Meta_reduceEval___rarg(x_1, x_52, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_box(0);
lean_ctor_set(x_8, 0, x_65);
return x_8;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_20);
lean_free_object(x_8);
lean_dec(x_1);
x_66 = lean_box(0);
x_12 = x_66;
goto block_19;
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_13 = lean_expr_dbg_to_string(x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_throwError___rarg(x_17, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_77; 
x_67 = lean_ctor_get(x_8, 0);
x_68 = lean_ctor_get(x_8, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_8);
x_77 = l_Lean_Expr_getAppFn___main(x_67);
if (lean_obj_tag(x_77) == 4)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Lean_Expr_getAppNumArgsAux___main(x_67, x_79);
x_81 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
x_82 = lean_name_eq(x_78, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_84 = lean_name_eq(x_78, x_83);
lean_dec(x_78);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_1);
x_85 = lean_box(0);
x_69 = x_85;
goto block_76;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_dec_eq(x_80, x_86);
lean_dec(x_80);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_1);
x_88 = lean_box(0);
x_69 = x_88;
goto block_76;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_90 = l_Lean_Meta_reduceEval___rarg(x_1, x_89, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_eq(x_80, x_79);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_102 = lean_name_eq(x_78, x_101);
lean_dec(x_78);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_80);
lean_dec(x_1);
x_103 = lean_box(0);
x_69 = x_103;
goto block_76;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_dec_eq(x_80, x_104);
lean_dec(x_80);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_1);
x_106 = lean_box(0);
x_69 = x_106;
goto block_76;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_108 = l_Lean_Meta_reduceEval___rarg(x_1, x_107, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_109);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_116 = x_108;
} else {
 lean_dec_ref(x_108);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_68);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_77);
lean_dec(x_1);
x_120 = lean_box(0);
x_69 = x_120;
goto block_76;
}
block_76:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
x_70 = lean_expr_dbg_to_string(x_67);
lean_dec(x_67);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Meta_throwError___rarg(x_74, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_75;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_8);
if (x_121 == 0)
{
return x_8;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_8, 0);
x_123 = lean_ctor_get(x_8, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_8);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
lean_object* l_Lean_Meta_Option_hasReduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Option_hasReduceEval___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_String_hasReduceEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_9) == 9)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_19);
lean_free_object(x_7);
x_20 = lean_box(0);
x_11 = x_20;
goto block_18;
}
else
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; 
lean_free_object(x_7);
lean_dec(x_9);
x_22 = lean_box(0);
x_11 = x_22;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_12 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_throwError___rarg(x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
if (lean_obj_tag(x_23) == 9)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_33);
x_34 = lean_box(0);
x_25 = x_34;
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_23);
x_37 = lean_box(0);
x_25 = x_37;
goto block_32;
}
block_32:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_26 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_throwError___rarg(x_30, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_31;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
return x_7;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get_uint8(x_8, 5);
x_11 = 1;
x_12 = l_Lean_Meta_TransparencyMode_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_Meta_evalNat___main(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_13);
x_18 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_throwError___rarg(x_22, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
lean_inc(x_25);
x_27 = l_Lean_Meta_evalNat___main(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_expr_dbg_to_string(x_25);
lean_dec(x_25);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_throwError___rarg(x_32, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_ctor_set_uint8(x_8, 5, x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_44 = l_Lean_Meta_evalNat___main(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_40);
x_45 = lean_expr_dbg_to_string(x_42);
lean_dec(x_42);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_throwError___rarg(x_49, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
lean_inc(x_52);
x_54 = l_Lean_Meta_evalNat___main(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_expr_dbg_to_string(x_52);
lean_dec(x_52);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Meta_throwError___rarg(x_59, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_40);
if (x_63 == 0)
{
return x_40;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_40, 0);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_40);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; 
x_67 = lean_ctor_get_uint8(x_8, 0);
x_68 = lean_ctor_get_uint8(x_8, 1);
x_69 = lean_ctor_get_uint8(x_8, 2);
x_70 = lean_ctor_get_uint8(x_8, 3);
x_71 = lean_ctor_get_uint8(x_8, 4);
x_72 = lean_ctor_get_uint8(x_8, 5);
lean_dec(x_8);
x_73 = 1;
x_74 = l_Lean_Meta_TransparencyMode_lt(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_75, 0, x_67);
lean_ctor_set_uint8(x_75, 1, x_68);
lean_ctor_set_uint8(x_75, 2, x_69);
lean_ctor_set_uint8(x_75, 3, x_70);
lean_ctor_set_uint8(x_75, 4, x_71);
lean_ctor_set_uint8(x_75, 5, x_72);
lean_ctor_set(x_2, 0, x_75);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_76 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
lean_inc(x_77);
x_80 = l_Lean_Meta_evalNat___main(x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_79);
x_81 = lean_expr_dbg_to_string(x_77);
lean_dec(x_77);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Meta_throwError___rarg(x_85, x_2, x_3, x_4, x_5, x_78);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_77);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
lean_dec(x_80);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_91 = x_76;
} else {
 lean_dec_ref(x_76);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_93, 0, x_67);
lean_ctor_set_uint8(x_93, 1, x_68);
lean_ctor_set_uint8(x_93, 2, x_69);
lean_ctor_set_uint8(x_93, 3, x_70);
lean_ctor_set_uint8(x_93, 4, x_71);
lean_ctor_set_uint8(x_93, 5, x_73);
lean_ctor_set(x_2, 0, x_93);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_94 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
lean_inc(x_95);
x_98 = l_Lean_Meta_evalNat___main(x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_97);
x_99 = lean_expr_dbg_to_string(x_95);
lean_dec(x_95);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Meta_throwError___rarg(x_103, x_2, x_3, x_4, x_5, x_96);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_95);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_98, 0);
lean_inc(x_105);
lean_dec(x_98);
if (lean_is_scalar(x_97)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_97;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_96);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_94, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_94, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_109 = x_94;
} else {
 lean_dec_ref(x_94);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_2, 0);
x_112 = lean_ctor_get(x_2, 1);
x_113 = lean_ctor_get(x_2, 2);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_2);
x_114 = lean_ctor_get_uint8(x_111, 0);
x_115 = lean_ctor_get_uint8(x_111, 1);
x_116 = lean_ctor_get_uint8(x_111, 2);
x_117 = lean_ctor_get_uint8(x_111, 3);
x_118 = lean_ctor_get_uint8(x_111, 4);
x_119 = lean_ctor_get_uint8(x_111, 5);
if (lean_is_exclusive(x_111)) {
 x_120 = x_111;
} else {
 lean_dec_ref(x_111);
 x_120 = lean_box(0);
}
x_121 = 1;
x_122 = l_Lean_Meta_TransparencyMode_lt(x_119, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 0, 6);
} else {
 x_123 = x_120;
}
lean_ctor_set_uint8(x_123, 0, x_114);
lean_ctor_set_uint8(x_123, 1, x_115);
lean_ctor_set_uint8(x_123, 2, x_116);
lean_ctor_set_uint8(x_123, 3, x_117);
lean_ctor_set_uint8(x_123, 4, x_118);
lean_ctor_set_uint8(x_123, 5, x_119);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_112);
lean_ctor_set(x_124, 2, x_113);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_124);
x_125 = l_Lean_Meta_whnf(x_1, x_124, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
lean_inc(x_126);
x_129 = l_Lean_Meta_evalNat___main(x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_128);
x_130 = lean_expr_dbg_to_string(x_126);
lean_dec(x_126);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lean_Meta_throwError___rarg(x_134, x_124, x_3, x_4, x_5, x_127);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_124);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
lean_dec(x_129);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_127);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_125, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_125, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_140 = x_125;
} else {
 lean_dec_ref(x_125);
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
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
if (lean_is_scalar(x_120)) {
 x_142 = lean_alloc_ctor(0, 0, 6);
} else {
 x_142 = x_120;
}
lean_ctor_set_uint8(x_142, 0, x_114);
lean_ctor_set_uint8(x_142, 1, x_115);
lean_ctor_set_uint8(x_142, 2, x_116);
lean_ctor_set_uint8(x_142, 3, x_117);
lean_ctor_set_uint8(x_142, 4, x_118);
lean_ctor_set_uint8(x_142, 5, x_121);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_112);
lean_ctor_set(x_143, 2, x_113);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_143);
x_144 = l_Lean_Meta_whnf(x_1, x_143, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
lean_inc(x_145);
x_148 = l_Lean_Meta_evalNat___main(x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
x_149 = lean_expr_dbg_to_string(x_145);
lean_dec(x_145);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Meta_throwError___rarg(x_153, x_143, x_3, x_4, x_5, x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_143);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
lean_dec(x_148);
if (lean_is_scalar(x_147)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_147;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_146);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_144, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_159 = x_144;
} else {
 lean_dec_ref(x_144);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get_uint8(x_8, 5);
x_11 = 1;
x_12 = l_Lean_Meta_TransparencyMode_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
if (lean_obj_tag(x_15) == 9)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_25);
lean_free_object(x_13);
x_26 = lean_box(0);
x_17 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; 
lean_free_object(x_13);
lean_dec(x_15);
x_28 = lean_box(0);
x_17 = x_28;
goto block_24;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_18 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_throwError___rarg(x_22, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
if (lean_obj_tag(x_29) == 9)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_39);
x_40 = lean_box(0);
x_31 = x_40;
goto block_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_29);
x_43 = lean_box(0);
x_31 = x_43;
goto block_38;
}
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
x_32 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Meta_throwError___rarg(x_36, x_2, x_3, x_4, x_5, x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_ctor_set_uint8(x_8, 5, x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
if (lean_obj_tag(x_50) == 9)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_60);
lean_free_object(x_48);
x_61 = lean_box(0);
x_52 = x_61;
goto block_59;
}
else
{
lean_object* x_62; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_ctor_set(x_48, 0, x_62);
return x_48;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_48);
lean_dec(x_50);
x_63 = lean_box(0);
x_52 = x_63;
goto block_59;
}
block_59:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
x_53 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_throwError___rarg(x_57, x_2, x_3, x_4, x_5, x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_58;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_48, 0);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_48);
if (lean_obj_tag(x_64) == 9)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_74);
x_75 = lean_box(0);
x_66 = x_75;
goto block_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_65);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_64);
x_78 = lean_box(0);
x_66 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_66);
x_67 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Meta_throwError___rarg(x_71, x_2, x_3, x_4, x_5, x_65);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_72;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_48);
if (x_79 == 0)
{
return x_48;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_48, 0);
x_81 = lean_ctor_get(x_48, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_48);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_83 = lean_ctor_get_uint8(x_8, 0);
x_84 = lean_ctor_get_uint8(x_8, 1);
x_85 = lean_ctor_get_uint8(x_8, 2);
x_86 = lean_ctor_get_uint8(x_8, 3);
x_87 = lean_ctor_get_uint8(x_8, 4);
x_88 = lean_ctor_get_uint8(x_8, 5);
lean_dec(x_8);
x_89 = 1;
x_90 = l_Lean_Meta_TransparencyMode_lt(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_91, 0, x_83);
lean_ctor_set_uint8(x_91, 1, x_84);
lean_ctor_set_uint8(x_91, 2, x_85);
lean_ctor_set_uint8(x_91, 3, x_86);
lean_ctor_set_uint8(x_91, 4, x_87);
lean_ctor_set_uint8(x_91, 5, x_88);
lean_ctor_set(x_2, 0, x_91);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_92 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_obj_tag(x_93) == 9)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
lean_dec(x_93);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_dec(x_104);
lean_dec(x_95);
x_105 = lean_box(0);
x_96 = x_105;
goto block_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
if (lean_is_scalar(x_95)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_95;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_94);
return x_107;
}
}
else
{
lean_object* x_108; 
lean_dec(x_95);
lean_dec(x_93);
x_108 = lean_box(0);
x_96 = x_108;
goto block_103;
}
block_103:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_96);
x_97 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Meta_throwError___rarg(x_101, x_2, x_3, x_4, x_5, x_94);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_102;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = lean_ctor_get(x_92, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_92, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_111 = x_92;
} else {
 lean_dec_ref(x_92);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_113, 0, x_83);
lean_ctor_set_uint8(x_113, 1, x_84);
lean_ctor_set_uint8(x_113, 2, x_85);
lean_ctor_set_uint8(x_113, 3, x_86);
lean_ctor_set_uint8(x_113, 4, x_87);
lean_ctor_set_uint8(x_113, 5, x_89);
lean_ctor_set(x_2, 0, x_113);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
if (lean_obj_tag(x_115) == 9)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_115, 0);
lean_inc(x_126);
lean_dec(x_115);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_dec(x_126);
lean_dec(x_117);
x_127 = lean_box(0);
x_118 = x_127;
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
if (lean_is_scalar(x_117)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_117;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
return x_129;
}
}
else
{
lean_object* x_130; 
lean_dec(x_117);
lean_dec(x_115);
x_130 = lean_box(0);
x_118 = x_130;
goto block_125;
}
block_125:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_118);
x_119 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_throwError___rarg(x_123, x_2, x_3, x_4, x_5, x_116);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_124;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_131 = lean_ctor_get(x_114, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_114, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_133 = x_114;
} else {
 lean_dec_ref(x_114);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_135 = lean_ctor_get(x_2, 0);
x_136 = lean_ctor_get(x_2, 1);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_2);
x_138 = lean_ctor_get_uint8(x_135, 0);
x_139 = lean_ctor_get_uint8(x_135, 1);
x_140 = lean_ctor_get_uint8(x_135, 2);
x_141 = lean_ctor_get_uint8(x_135, 3);
x_142 = lean_ctor_get_uint8(x_135, 4);
x_143 = lean_ctor_get_uint8(x_135, 5);
if (lean_is_exclusive(x_135)) {
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
x_145 = 1;
x_146 = l_Lean_Meta_TransparencyMode_lt(x_143, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 0, 6);
} else {
 x_147 = x_144;
}
lean_ctor_set_uint8(x_147, 0, x_138);
lean_ctor_set_uint8(x_147, 1, x_139);
lean_ctor_set_uint8(x_147, 2, x_140);
lean_ctor_set_uint8(x_147, 3, x_141);
lean_ctor_set_uint8(x_147, 4, x_142);
lean_ctor_set_uint8(x_147, 5, x_143);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_136);
lean_ctor_set(x_148, 2, x_137);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_148);
lean_inc(x_1);
x_149 = l_Lean_Meta_whnf(x_1, x_148, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
if (lean_obj_tag(x_150) == 9)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
lean_dec(x_150);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
lean_dec(x_161);
lean_dec(x_152);
x_162 = lean_box(0);
x_153 = x_162;
goto block_160;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_148);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
if (lean_is_scalar(x_152)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_152;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_151);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec(x_152);
lean_dec(x_150);
x_165 = lean_box(0);
x_153 = x_165;
goto block_160;
}
block_160:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_153);
x_154 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_158 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Lean_Meta_throwError___rarg(x_158, x_148, x_3, x_4, x_5, x_151);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_148);
return x_159;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_148);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_166 = lean_ctor_get(x_149, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_scalar(x_144)) {
 x_170 = lean_alloc_ctor(0, 0, 6);
} else {
 x_170 = x_144;
}
lean_ctor_set_uint8(x_170, 0, x_138);
lean_ctor_set_uint8(x_170, 1, x_139);
lean_ctor_set_uint8(x_170, 2, x_140);
lean_ctor_set_uint8(x_170, 3, x_141);
lean_ctor_set_uint8(x_170, 4, x_142);
lean_ctor_set_uint8(x_170, 5, x_145);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_136);
lean_ctor_set(x_171, 2, x_137);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_171);
lean_inc(x_1);
x_172 = l_Lean_Meta_whnf(x_1, x_171, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_obj_tag(x_173) == 9)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_173, 0);
lean_inc(x_184);
lean_dec(x_173);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
lean_dec(x_184);
lean_dec(x_175);
x_185 = lean_box(0);
x_176 = x_185;
goto block_183;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
lean_dec(x_184);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_174);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_175);
lean_dec(x_173);
x_188 = lean_box(0);
x_176 = x_188;
goto block_183;
}
block_183:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_176);
x_177 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_Meta_throwError___rarg(x_181, x_171, x_3, x_4, x_5, x_174);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_171);
return x_182;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_189 = lean_ctor_get(x_172, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_172, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_191 = x_172;
} else {
 lean_dec_ref(x_172);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Lean_Syntax_7__quoteName___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l___private_Lean_Syntax_7__quoteName___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_19 = l_Lean_Expr_getAppFn___main(x_9);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_57; lean_object* x_91; uint8_t x_92; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_21);
x_91 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6;
x_92 = lean_name_eq(x_20, x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_free_object(x_7);
x_93 = lean_box(0);
x_57 = x_93;
goto block_90;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_eq(x_22, x_21);
if (x_94 == 0)
{
lean_object* x_95; 
lean_free_object(x_7);
x_95 = lean_box(0);
x_57 = x_95;
goto block_90;
}
else
{
lean_object* x_96; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_box(0);
lean_ctor_set(x_7, 0, x_96);
return x_7;
}
}
block_56:
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_23);
x_24 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3;
x_25 = lean_name_eq(x_20, x_24);
lean_dec(x_20);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = lean_box(0);
x_11 = x_26;
goto block_18;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_dec_eq(x_22, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
x_29 = lean_box(0);
x_11 = x_29;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_nat_sub(x_22, x_21);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_9, x_32);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_33, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_sub(x_22, x_31);
lean_dec(x_22);
x_38 = lean_nat_sub(x_37, x_31);
lean_dec(x_37);
x_39 = l_Lean_Expr_getRevArg_x21___main(x_9, x_38);
lean_dec(x_9);
x_40 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(x_39, x_2, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_name_mk_numeral(x_35, x_42);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_name_mk_numeral(x_35, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_35);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
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
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
block_90:
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_57);
x_58 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5;
x_59 = lean_name_eq(x_20, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_23 = x_60;
goto block_56;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_dec_eq(x_22, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_23 = x_63;
goto block_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_20);
x_64 = lean_nat_sub(x_22, x_21);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_64, x_65);
lean_dec(x_64);
x_67 = l_Lean_Expr_getRevArg_x21___main(x_9, x_66);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_68 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_67, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_nat_sub(x_22, x_65);
lean_dec(x_22);
x_72 = lean_nat_sub(x_71, x_65);
lean_dec(x_71);
x_73 = l_Lean_Expr_getRevArg_x21___main(x_9, x_72);
lean_dec(x_9);
x_74 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(x_73, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_name_mk_string(x_69, x_76);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_name_mk_string(x_69, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_69);
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
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
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_68);
if (x_86 == 0)
{
return x_68;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_68, 0);
x_88 = lean_ctor_get(x_68, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_68);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_19);
lean_free_object(x_7);
x_97 = lean_box(0);
x_11 = x_97;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_12 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_throwError___rarg(x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_108; 
x_98 = lean_ctor_get(x_7, 0);
x_99 = lean_ctor_get(x_7, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_7);
x_108 = l_Lean_Expr_getAppFn___main(x_98);
if (lean_obj_tag(x_108) == 4)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_144; lean_object* x_176; uint8_t x_177; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Lean_Expr_getAppNumArgsAux___main(x_98, x_110);
x_176 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6;
x_177 = lean_name_eq(x_109, x_176);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_box(0);
x_144 = x_178;
goto block_175;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_eq(x_111, x_110);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_box(0);
x_144 = x_180;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_99);
return x_182;
}
}
block_143:
{
lean_object* x_113; uint8_t x_114; 
lean_dec(x_112);
x_113 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3;
x_114 = lean_name_eq(x_109, x_113);
lean_dec(x_109);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_111);
x_115 = lean_box(0);
x_100 = x_115;
goto block_107;
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_unsigned_to_nat(3u);
x_117 = lean_nat_dec_eq(x_111, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_111);
x_118 = lean_box(0);
x_100 = x_118;
goto block_107;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_nat_sub(x_111, x_110);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_sub(x_119, x_120);
lean_dec(x_119);
x_122 = l_Lean_Expr_getRevArg_x21___main(x_98, x_121);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_123 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_122, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_nat_sub(x_111, x_120);
lean_dec(x_111);
x_127 = lean_nat_sub(x_126, x_120);
lean_dec(x_126);
x_128 = l_Lean_Expr_getRevArg_x21___main(x_98, x_127);
lean_dec(x_98);
x_129 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(x_128, x_2, x_3, x_4, x_5, x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_name_mk_numeral(x_124, x_130);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_124);
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_111);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_123, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_123, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_141 = x_123;
} else {
 lean_dec_ref(x_123);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
}
block_175:
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_144);
x_145 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5;
x_146 = lean_name_eq(x_109, x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_112 = x_147;
goto block_143;
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_dec_eq(x_111, x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_112 = x_150;
goto block_143;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_109);
x_151 = lean_nat_sub(x_111, x_110);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_sub(x_151, x_152);
lean_dec(x_151);
x_154 = l_Lean_Expr_getRevArg_x21___main(x_98, x_153);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_155 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_154, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_nat_sub(x_111, x_152);
lean_dec(x_111);
x_159 = lean_nat_sub(x_158, x_152);
lean_dec(x_158);
x_160 = l_Lean_Expr_getRevArg_x21___main(x_98, x_159);
lean_dec(x_98);
x_161 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(x_160, x_2, x_3, x_4, x_5, x_157);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_name_mk_string(x_156, x_162);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_156);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
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
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_111);
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_155, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_173 = x_155;
} else {
 lean_dec_ref(x_155);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
}
else
{
lean_object* x_183; 
lean_dec(x_108);
x_183 = lean_box(0);
x_100 = x_183;
goto block_107;
}
block_107:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_100);
x_101 = lean_expr_dbg_to_string(x_98);
lean_dec(x_98);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_Meta_throwError___rarg(x_105, x_2, x_3, x_4, x_5, x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_106;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_7);
if (x_184 == 0)
{
return x_7;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_7, 0);
x_186 = lean_ctor_get(x_7, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_7);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_Name_hasReduceEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_1__evalName), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Name_hasReduceEval() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Name_hasReduceEval___closed__1;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Offset(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_ReduceEval(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Nat_hasReduceEval___closed__1 = _init_l_Lean_Meta_Nat_hasReduceEval___closed__1();
lean_mark_persistent(l_Lean_Meta_Nat_hasReduceEval___closed__1);
l_Lean_Meta_Nat_hasReduceEval___closed__2 = _init_l_Lean_Meta_Nat_hasReduceEval___closed__2();
lean_mark_persistent(l_Lean_Meta_Nat_hasReduceEval___closed__2);
l_Lean_Meta_Nat_hasReduceEval___closed__3 = _init_l_Lean_Meta_Nat_hasReduceEval___closed__3();
lean_mark_persistent(l_Lean_Meta_Nat_hasReduceEval___closed__3);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__5);
l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6 = _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__6);
l_Lean_Meta_Name_hasReduceEval___closed__1 = _init_l_Lean_Meta_Name_hasReduceEval___closed__1();
lean_mark_persistent(l_Lean_Meta_Name_hasReduceEval___closed__1);
l_Lean_Meta_Name_hasReduceEval = _init_l_Lean_Meta_Name_hasReduceEval();
lean_mark_persistent(l_Lean_Meta_Name_hasReduceEval);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
