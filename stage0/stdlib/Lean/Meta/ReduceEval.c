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
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2;
lean_object* l_Lean_Meta_Nat_hasReduceEval(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Nat_hasReduceEval___closed__3;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_HasQuote___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat___main(lean_object*);
extern lean_object* l_Lean_String_HasQuote___closed__1;
extern lean_object* l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Meta_Option_hasReduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_String_hasReduceEval(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Name_hasReduceEval___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
x_9 = 1;
x_10 = l_Lean_Meta_TransparencyMode_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; 
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 6, x_9);
x_12 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
lean_inc(x_13);
lean_dec(x_6);
x_21 = 1;
x_22 = l_Lean_Meta_TransparencyMode_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 5, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 6, x_20);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 5, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 6, x_21);
lean_ctor_set(x_3, 0, x_25);
x_26 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_3, 2);
x_30 = lean_ctor_get(x_3, 3);
x_31 = lean_ctor_get(x_3, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
x_34 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 2);
x_36 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 3);
x_37 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 4);
x_38 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 5);
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_40 = x_27;
} else {
 lean_dec_ref(x_27);
 x_40 = lean_box(0);
}
x_41 = 1;
x_42 = l_Lean_Meta_TransparencyMode_lt(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 7);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_33);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 1, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 2, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 3, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 4, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 5, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 6, x_39);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
x_45 = lean_apply_3(x_1, x_2, x_44, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(0, 1, 7);
} else {
 x_46 = x_40;
}
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 1, x_34);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 2, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 3, x_36);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 4, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 5, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*1 + 6, x_41);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_28);
lean_ctor_set(x_47, 2, x_29);
lean_ctor_set(x_47, 3, x_30);
lean_ctor_set(x_47, 4, x_31);
x_48 = lean_apply_3(x_1, x_2, x_47, x_4);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_reduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceEval___rarg), 4, 0);
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
lean_object* l_Lean_Meta_Nat_hasReduceEval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = l_Lean_Meta_evalNat___main(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
x_9 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwOther___rarg(x_13, x_14, x_2, x_7);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_17);
x_19 = l_Lean_Meta_evalNat___main(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_expr_dbg_to_string(x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwOther___rarg(x_24, x_25, x_2, x_18);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_2);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_Option_hasReduceEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Meta_whnf(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_18 = l_Lean_Expr_getAppFn___main(x_7);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_20);
x_22 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
x_23 = lean_name_eq(x_19, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_free_object(x_5);
x_24 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_25 = lean_name_eq(x_19, x_24);
lean_dec(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_1);
x_26 = lean_box(0);
x_9 = x_26;
goto block_17;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_21, x_27);
lean_dec(x_21);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_box(0);
x_9 = x_29;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_31 = l_Lean_Meta_reduceEval___rarg(x_1, x_30, x_3, x_8);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_21, x_20);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_free_object(x_5);
x_44 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_45 = lean_name_eq(x_19, x_44);
lean_dec(x_19);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_21);
lean_dec(x_1);
x_46 = lean_box(0);
x_9 = x_46;
goto block_17;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_dec_eq(x_21, x_47);
lean_dec(x_21);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = lean_box(0);
x_9 = x_49;
goto block_17;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_51 = l_Lean_Meta_reduceEval___rarg(x_1, x_50, x_3, x_8);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
lean_ctor_set(x_5, 0, x_63);
return x_5;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_1);
x_64 = lean_box(0);
x_9 = x_64;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_10 = lean_expr_dbg_to_string(x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwOther___rarg(x_14, x_15, x_3, x_8);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_76; 
x_65 = lean_ctor_get(x_5, 0);
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_5);
x_76 = l_Lean_Expr_getAppFn___main(x_65);
if (lean_obj_tag(x_76) == 4)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Expr_getAppNumArgsAux___main(x_65, x_78);
x_80 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__3;
x_81 = lean_name_eq(x_77, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_83 = lean_name_eq(x_77, x_82);
lean_dec(x_77);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_79);
lean_dec(x_1);
x_84 = lean_box(0);
x_67 = x_84;
goto block_75;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_dec_eq(x_79, x_85);
lean_dec(x_79);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_1);
x_87 = lean_box(0);
x_67 = x_87;
goto block_75;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_89 = l_Lean_Meta_reduceEval___rarg(x_1, x_88, x_3, x_66);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_eq(x_79, x_78);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = l___private_Lean_Syntax_9__quoteOption___rarg___closed__6;
x_101 = lean_name_eq(x_77, x_100);
lean_dec(x_77);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_1);
x_102 = lean_box(0);
x_67 = x_102;
goto block_75;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_eq(x_79, x_103);
lean_dec(x_79);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_1);
x_105 = lean_box(0);
x_67 = x_105;
goto block_75;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_107 = l_Lean_Meta_reduceEval___rarg(x_1, x_106, x_3, x_66);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_66);
return x_118;
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_76);
lean_dec(x_1);
x_119 = lean_box(0);
x_67 = x_119;
goto block_75;
}
block_75:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
x_68 = lean_expr_dbg_to_string(x_65);
lean_dec(x_65);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_box(0);
x_74 = l_Lean_Meta_throwOther___rarg(x_72, x_73, x_3, x_66);
lean_dec(x_3);
return x_74;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_3);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_5);
if (x_120 == 0)
{
return x_5;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Meta_Option_hasReduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Option_hasReduceEval___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_String_hasReduceEval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_6) == 9)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_17);
lean_free_object(x_4);
x_18 = lean_box(0);
x_8 = x_18;
goto block_16;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
}
else
{
lean_object* x_20; 
lean_free_object(x_4);
lean_dec(x_6);
x_20 = lean_box(0);
x_8 = x_20;
goto block_16;
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_9 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwOther___rarg(x_13, x_14, x_2, x_7);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 9)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_32);
x_33 = lean_box(0);
x_23 = x_33;
goto block_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_21);
x_36 = lean_box(0);
x_23 = x_36;
goto block_31;
}
block_31:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_24 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwOther___rarg(x_28, x_29, x_2, x_22);
lean_dec(x_2);
return x_30;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
x_8 = 1;
x_9 = l_Lean_Meta_TransparencyMode_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_14 = l_Lean_Meta_evalNat___main(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_10);
x_15 = lean_expr_dbg_to_string(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwOther___rarg(x_19, x_20, x_2, x_13);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_2);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_23);
x_25 = l_Lean_Meta_evalNat___main(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_expr_dbg_to_string(x_23);
lean_dec(x_23);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_throwOther___rarg(x_30, x_31, x_2, x_24);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_2);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_8);
lean_inc(x_2);
x_39 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_43 = l_Lean_Meta_evalNat___main(x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_39);
x_44 = lean_expr_dbg_to_string(x_41);
lean_dec(x_41);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_throwOther___rarg(x_48, x_49, x_2, x_42);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_2);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
lean_ctor_set(x_39, 0, x_51);
return x_39;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
lean_inc(x_52);
x_54 = l_Lean_Meta_evalNat___main(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwOther___rarg(x_59, x_60, x_2, x_53);
lean_dec(x_2);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_52);
lean_dec(x_2);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_39);
if (x_64 == 0)
{
return x_39;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_39, 0);
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_39);
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
lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_72 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_73 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_74 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_75 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_68);
lean_dec(x_5);
x_76 = 1;
x_77 = l_Lean_Meta_TransparencyMode_lt(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_69);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 1, x_70);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 2, x_71);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 4, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 5, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*1 + 6, x_75);
lean_ctor_set(x_2, 0, x_78);
lean_inc(x_2);
x_79 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
lean_inc(x_80);
x_83 = l_Lean_Meta_evalNat___main(x_80);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
x_84 = lean_expr_dbg_to_string(x_80);
lean_dec(x_80);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_88 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_box(0);
x_90 = l_Lean_Meta_throwOther___rarg(x_88, x_89, x_2, x_81);
lean_dec(x_2);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_80);
lean_dec(x_2);
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
lean_dec(x_83);
if (lean_is_scalar(x_82)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_82;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
x_93 = lean_ctor_get(x_79, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_95 = x_79;
} else {
 lean_dec_ref(x_79);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_97, 0, x_68);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_69);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 1, x_70);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 2, x_71);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 3, x_72);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 4, x_73);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 5, x_74);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 6, x_76);
lean_ctor_set(x_2, 0, x_97);
lean_inc(x_2);
x_98 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
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
lean_inc(x_99);
x_102 = l_Lean_Meta_evalNat___main(x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
x_103 = lean_expr_dbg_to_string(x_99);
lean_dec(x_99);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_107 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_box(0);
x_109 = l_Lean_Meta_throwOther___rarg(x_107, x_108, x_2, x_100);
lean_dec(x_2);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_99);
lean_dec(x_2);
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
lean_dec(x_102);
if (lean_is_scalar(x_101)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_101;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_100);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_112 = lean_ctor_get(x_98, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_114 = x_98;
} else {
 lean_dec_ref(x_98);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; 
x_116 = lean_ctor_get(x_2, 0);
x_117 = lean_ctor_get(x_2, 1);
x_118 = lean_ctor_get(x_2, 2);
x_119 = lean_ctor_get(x_2, 3);
x_120 = lean_ctor_get(x_2, 4);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_2);
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_116, sizeof(void*)*1);
x_123 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 1);
x_124 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 2);
x_125 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 3);
x_126 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 4);
x_127 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 5);
x_128 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_129 = x_116;
} else {
 lean_dec_ref(x_116);
 x_129 = lean_box(0);
}
x_130 = 1;
x_131 = l_Lean_Meta_TransparencyMode_lt(x_128, x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 1, 7);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_122);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 1, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 2, x_124);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 3, x_125);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 4, x_126);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 5, x_127);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 6, x_128);
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_117);
lean_ctor_set(x_133, 2, x_118);
lean_ctor_set(x_133, 3, x_119);
lean_ctor_set(x_133, 4, x_120);
lean_inc(x_133);
x_134 = l_Lean_Meta_whnf(x_1, x_133, x_3);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
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
lean_inc(x_135);
x_138 = l_Lean_Meta_evalNat___main(x_135);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_137);
x_139 = lean_expr_dbg_to_string(x_135);
lean_dec(x_135);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_box(0);
x_145 = l_Lean_Meta_throwOther___rarg(x_143, x_144, x_133, x_136);
lean_dec(x_133);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_135);
lean_dec(x_133);
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
lean_dec(x_138);
if (lean_is_scalar(x_137)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_137;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_136);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
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
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_scalar(x_129)) {
 x_152 = lean_alloc_ctor(0, 1, 7);
} else {
 x_152 = x_129;
}
lean_ctor_set(x_152, 0, x_121);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_122);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 1, x_123);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 2, x_124);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 3, x_125);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 4, x_126);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 5, x_127);
lean_ctor_set_uint8(x_152, sizeof(void*)*1 + 6, x_130);
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_117);
lean_ctor_set(x_153, 2, x_118);
lean_ctor_set(x_153, 3, x_119);
lean_ctor_set(x_153, 4, x_120);
lean_inc(x_153);
x_154 = l_Lean_Meta_whnf(x_1, x_153, x_3);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
lean_inc(x_155);
x_158 = l_Lean_Meta_evalNat___main(x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_157);
x_159 = lean_expr_dbg_to_string(x_155);
lean_dec(x_155);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_box(0);
x_165 = l_Lean_Meta_throwOther___rarg(x_163, x_164, x_153, x_156);
lean_dec(x_153);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_155);
lean_dec(x_153);
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_166);
lean_dec(x_158);
if (lean_is_scalar(x_157)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_157;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_156);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
x_168 = lean_ctor_get(x_154, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_170 = x_154;
} else {
 lean_dec_ref(x_154);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
x_8 = 1;
x_9 = l_Lean_Meta_TransparencyMode_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
if (lean_obj_tag(x_12) == 9)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_23);
lean_free_object(x_10);
x_24 = lean_box(0);
x_14 = x_24;
goto block_22;
}
else
{
lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; 
lean_free_object(x_10);
lean_dec(x_12);
x_26 = lean_box(0);
x_14 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_15 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwOther___rarg(x_19, x_20, x_2, x_13);
lean_dec(x_2);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
if (lean_obj_tag(x_27) == 9)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_38);
x_39 = lean_box(0);
x_29 = x_39;
goto block_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_27);
x_42 = lean_box(0);
x_29 = x_42;
goto block_37;
}
block_37:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
x_30 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_box(0);
x_36 = l_Lean_Meta_throwOther___rarg(x_34, x_35, x_2, x_28);
lean_dec(x_2);
return x_36;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
if (lean_obj_tag(x_49) == 9)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
lean_dec(x_49);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec(x_60);
lean_free_object(x_47);
x_61 = lean_box(0);
x_51 = x_61;
goto block_59;
}
else
{
lean_object* x_62; 
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_ctor_set(x_47, 0, x_62);
return x_47;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_47);
lean_dec(x_49);
x_63 = lean_box(0);
x_51 = x_63;
goto block_59;
}
block_59:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
x_52 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_throwOther___rarg(x_56, x_57, x_2, x_50);
lean_dec(x_2);
return x_58;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_47, 0);
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_47);
if (lean_obj_tag(x_64) == 9)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_75);
x_76 = lean_box(0);
x_66 = x_76;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_65);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_64);
x_79 = lean_box(0);
x_66 = x_79;
goto block_74;
}
block_74:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_72 = lean_box(0);
x_73 = l_Lean_Meta_throwOther___rarg(x_71, x_72, x_2, x_65);
lean_dec(x_2);
return x_73;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
return x_47;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_47, 0);
x_82 = lean_ctor_get(x_47, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_47);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; 
x_84 = lean_ctor_get(x_5, 0);
x_85 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_88 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_89 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_90 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_91 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_84);
lean_dec(x_5);
x_92 = 1;
x_93 = l_Lean_Meta_TransparencyMode_lt(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_94, 0, x_84);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_85);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_86);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 2, x_87);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 3, x_88);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 4, x_89);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 5, x_90);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 6, x_91);
lean_ctor_set(x_2, 0, x_94);
lean_inc(x_2);
lean_inc(x_1);
x_95 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_obj_tag(x_96) == 9)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
lean_dec(x_96);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_108);
lean_dec(x_98);
x_109 = lean_box(0);
x_99 = x_109;
goto block_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
if (lean_is_scalar(x_98)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_98;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_97);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_98);
lean_dec(x_96);
x_112 = lean_box(0);
x_99 = x_112;
goto block_107;
}
block_107:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
x_100 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_104 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_box(0);
x_106 = l_Lean_Meta_throwOther___rarg(x_104, x_105, x_2, x_97);
lean_dec(x_2);
return x_106;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_95, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_115 = x_95;
} else {
 lean_dec_ref(x_95);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_117, 0, x_84);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_85);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 1, x_86);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 2, x_87);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 3, x_88);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 4, x_89);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 5, x_90);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 6, x_92);
lean_ctor_set(x_2, 0, x_117);
lean_inc(x_2);
lean_inc(x_1);
x_118 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_obj_tag(x_119) == 9)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_119, 0);
lean_inc(x_131);
lean_dec(x_119);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
lean_dec(x_131);
lean_dec(x_121);
x_132 = lean_box(0);
x_122 = x_132;
goto block_130;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
if (lean_is_scalar(x_121)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_121;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
return x_134;
}
}
else
{
lean_object* x_135; 
lean_dec(x_121);
lean_dec(x_119);
x_135 = lean_box(0);
x_122 = x_135;
goto block_130;
}
block_130:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_122);
x_123 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_124 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_box(0);
x_129 = l_Lean_Meta_throwOther___rarg(x_127, x_128, x_2, x_120);
lean_dec(x_2);
return x_129;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_118, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_118, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_138 = x_118;
} else {
 lean_dec_ref(x_118);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; 
x_140 = lean_ctor_get(x_2, 0);
x_141 = lean_ctor_get(x_2, 1);
x_142 = lean_ctor_get(x_2, 2);
x_143 = lean_ctor_get(x_2, 3);
x_144 = lean_ctor_get(x_2, 4);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_2);
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_140, sizeof(void*)*1);
x_147 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 1);
x_148 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 2);
x_149 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 3);
x_150 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 4);
x_151 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 5);
x_152 = lean_ctor_get_uint8(x_140, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_153 = x_140;
} else {
 lean_dec_ref(x_140);
 x_153 = lean_box(0);
}
x_154 = 1;
x_155 = l_Lean_Meta_TransparencyMode_lt(x_152, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 1, 7);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_145);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_146);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 1, x_147);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 2, x_148);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 3, x_149);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 4, x_150);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 5, x_151);
lean_ctor_set_uint8(x_156, sizeof(void*)*1 + 6, x_152);
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_141);
lean_ctor_set(x_157, 2, x_142);
lean_ctor_set(x_157, 3, x_143);
lean_ctor_set(x_157, 4, x_144);
lean_inc(x_157);
lean_inc(x_1);
x_158 = l_Lean_Meta_whnf(x_1, x_157, x_3);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
if (lean_obj_tag(x_159) == 9)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_159, 0);
lean_inc(x_171);
lean_dec(x_159);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
lean_dec(x_171);
lean_dec(x_161);
x_172 = lean_box(0);
x_162 = x_172;
goto block_170;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_1);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
if (lean_is_scalar(x_161)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_161;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_160);
return x_174;
}
}
else
{
lean_object* x_175; 
lean_dec(x_161);
lean_dec(x_159);
x_175 = lean_box(0);
x_162 = x_175;
goto block_170;
}
block_170:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_162);
x_163 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_167 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_box(0);
x_169 = l_Lean_Meta_throwOther___rarg(x_167, x_168, x_157, x_160);
lean_dec(x_157);
return x_169;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_157);
lean_dec(x_1);
x_176 = lean_ctor_get(x_158, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_178 = x_158;
} else {
 lean_dec_ref(x_158);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
if (lean_is_scalar(x_153)) {
 x_180 = lean_alloc_ctor(0, 1, 7);
} else {
 x_180 = x_153;
}
lean_ctor_set(x_180, 0, x_145);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_146);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 1, x_147);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 2, x_148);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 3, x_149);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 4, x_150);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 5, x_151);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 6, x_154);
x_181 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_141);
lean_ctor_set(x_181, 2, x_142);
lean_ctor_set(x_181, 3, x_143);
lean_ctor_set(x_181, 4, x_144);
lean_inc(x_181);
lean_inc(x_1);
x_182 = l_Lean_Meta_whnf(x_1, x_181, x_3);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
if (lean_obj_tag(x_183) == 9)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_183, 0);
lean_inc(x_195);
lean_dec(x_183);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
lean_dec(x_195);
lean_dec(x_185);
x_196 = lean_box(0);
x_186 = x_196;
goto block_194;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_1);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
if (lean_is_scalar(x_185)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_185;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_184);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_185);
lean_dec(x_183);
x_199 = lean_box(0);
x_186 = x_199;
goto block_194;
}
block_194:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_186);
x_187 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_191 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = lean_box(0);
x_193 = l_Lean_Meta_throwOther___rarg(x_191, x_192, x_181, x_184);
lean_dec(x_181);
return x_193;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_181);
lean_dec(x_1);
x_200 = lean_ctor_get(x_182, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_202 = x_182;
} else {
 lean_dec_ref(x_182);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l_Lean_Nat_HasQuote___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l_Lean_String_HasQuote___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__1;
x_2 = l___private_Lean_Syntax_7__quoteName___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_17 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_55; lean_object* x_89; uint8_t x_90; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_19);
x_89 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4;
x_90 = lean_name_eq(x_18, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_free_object(x_4);
x_91 = lean_box(0);
x_55 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_eq(x_20, x_19);
if (x_92 == 0)
{
lean_object* x_93; 
lean_free_object(x_4);
x_93 = lean_box(0);
x_55 = x_93;
goto block_88;
}
else
{
lean_object* x_94; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_2);
x_94 = lean_box(0);
lean_ctor_set(x_4, 0, x_94);
return x_4;
}
}
block_54:
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_21);
x_22 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2;
x_23 = lean_name_eq(x_18, x_22);
lean_dec(x_18);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_box(0);
x_8 = x_24;
goto block_16;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_dec_eq(x_20, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_20);
x_27 = lean_box(0);
x_8 = x_27;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_nat_sub(x_20, x_19);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Expr_getRevArg_x21___main(x_6, x_30);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_31, x_2, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_nat_sub(x_20, x_29);
lean_dec(x_20);
x_36 = lean_nat_sub(x_35, x_29);
lean_dec(x_35);
x_37 = l_Lean_Expr_getRevArg_x21___main(x_6, x_36);
lean_dec(x_6);
x_38 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(x_37, x_2, x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_name_mk_numeral(x_33, x_40);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_name_mk_numeral(x_33, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_33);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
block_88:
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_55);
x_56 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3;
x_57 = lean_name_eq(x_18, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
x_21 = x_58;
goto block_54;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_dec_eq(x_20, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_21 = x_61;
goto block_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_18);
x_62 = lean_nat_sub(x_20, x_19);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_62, x_63);
lean_dec(x_62);
x_65 = l_Lean_Expr_getRevArg_x21___main(x_6, x_64);
lean_inc(x_2);
x_66 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_65, x_2, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_nat_sub(x_20, x_63);
lean_dec(x_20);
x_70 = lean_nat_sub(x_69, x_63);
lean_dec(x_69);
x_71 = l_Lean_Expr_getRevArg_x21___main(x_6, x_70);
lean_dec(x_6);
x_72 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(x_71, x_2, x_68);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_name_mk_string(x_67, x_74);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_name_mk_string(x_67, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_67);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
return x_72;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
return x_66;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_66);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_17);
lean_free_object(x_4);
x_95 = lean_box(0);
x_8 = x_95;
goto block_16;
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_9 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwOther___rarg(x_13, x_14, x_2, x_7);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_107; 
x_96 = lean_ctor_get(x_4, 0);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_4);
x_107 = l_Lean_Expr_getAppFn___main(x_96);
if (lean_obj_tag(x_107) == 4)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_143; lean_object* x_175; uint8_t x_176; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_109);
x_175 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__4;
x_176 = lean_name_eq(x_108, x_175);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_box(0);
x_143 = x_177;
goto block_174;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_eq(x_110, x_109);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_box(0);
x_143 = x_179;
goto block_174;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_96);
lean_dec(x_2);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_97);
return x_181;
}
}
block_142:
{
lean_object* x_112; uint8_t x_113; 
lean_dec(x_111);
x_112 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__2;
x_113 = lean_name_eq(x_108, x_112);
lean_dec(x_108);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_110);
x_114 = lean_box(0);
x_98 = x_114;
goto block_106;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_unsigned_to_nat(3u);
x_116 = lean_nat_dec_eq(x_110, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_110);
x_117 = lean_box(0);
x_98 = x_117;
goto block_106;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_nat_sub(x_110, x_109);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_118, x_119);
lean_dec(x_118);
x_121 = l_Lean_Expr_getRevArg_x21___main(x_96, x_120);
lean_inc(x_2);
x_122 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_121, x_2, x_97);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_nat_sub(x_110, x_119);
lean_dec(x_110);
x_126 = lean_nat_sub(x_125, x_119);
lean_dec(x_125);
x_127 = l_Lean_Expr_getRevArg_x21___main(x_96, x_126);
lean_dec(x_96);
x_128 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__1(x_127, x_2, x_124);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_name_mk_numeral(x_123, x_129);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_123);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_110);
lean_dec(x_96);
lean_dec(x_2);
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_122, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_140 = x_122;
} else {
 lean_dec_ref(x_122);
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
}
}
block_174:
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_143);
x_144 = l___private_Lean_Meta_ReduceEval_1__evalName___main___closed__3;
x_145 = lean_name_eq(x_108, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_111 = x_146;
goto block_142;
}
else
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_unsigned_to_nat(3u);
x_148 = lean_nat_dec_eq(x_110, x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_111 = x_149;
goto block_142;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_108);
x_150 = lean_nat_sub(x_110, x_109);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_sub(x_150, x_151);
lean_dec(x_150);
x_153 = l_Lean_Expr_getRevArg_x21___main(x_96, x_152);
lean_inc(x_2);
x_154 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_153, x_2, x_97);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_nat_sub(x_110, x_151);
lean_dec(x_110);
x_158 = lean_nat_sub(x_157, x_151);
lean_dec(x_157);
x_159 = l_Lean_Expr_getRevArg_x21___main(x_96, x_158);
lean_dec(x_96);
x_160 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_1__evalName___main___spec__2(x_159, x_2, x_156);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_name_mk_string(x_155, x_161);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_155);
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_168 = x_160;
} else {
 lean_dec_ref(x_160);
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
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_110);
lean_dec(x_96);
lean_dec(x_2);
x_170 = lean_ctor_get(x_154, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_154, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_172 = x_154;
} else {
 lean_dec_ref(x_154);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_107);
x_182 = lean_box(0);
x_98 = x_182;
goto block_106;
}
block_106:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
x_99 = lean_expr_dbg_to_string(x_96);
lean_dec(x_96);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_Meta_Nat_hasReduceEval___closed__3;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_throwOther___rarg(x_103, x_104, x_2, x_97);
lean_dec(x_2);
return x_105;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_4);
if (x_183 == 0)
{
return x_4;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_4, 0);
x_185 = lean_ctor_get(x_4, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_4);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
lean_object* l___private_Lean_Meta_ReduceEval_1__evalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_ReduceEval_1__evalName___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_Name_hasReduceEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_1__evalName), 3, 0);
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
l_Lean_Meta_Name_hasReduceEval___closed__1 = _init_l_Lean_Meta_Name_hasReduceEval___closed__1();
lean_mark_persistent(l_Lean_Meta_Name_hasReduceEval___closed__1);
l_Lean_Meta_Name_hasReduceEval = _init_l_Lean_Meta_Name_hasReduceEval();
lean_mark_persistent(l_Lean_Meta_Name_hasReduceEval);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
