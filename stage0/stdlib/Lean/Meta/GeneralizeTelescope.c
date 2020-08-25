// Lean compiler output
// Module: Lean.Meta.GeneralizeTelescope
// Imports: Init Lean.Meta.KAbstract
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
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main(lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_generalizeTelescope(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_generalizeTelescope___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Expr_toHeadIndex___main(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_st_mk_ref(x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_9, x_11, x_1, x_10, x_14, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1(x_16, x_1, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_hasLooseBVars(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_4 = x_23;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_expr_instantiate1(x_19, x_2);
lean_dec(x_19);
x_26 = 1;
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_26);
x_27 = lean_array_fset(x_3, x_4, x_13);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_3 = x_27;
x_4 = x_29;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_38 = l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1(x_36, x_1, x_37, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_hasLooseBVars(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_4, x_42);
lean_dec(x_4);
x_4 = x_43;
x_9 = x_40;
goto _start;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_expr_instantiate1(x_39, x_2);
lean_dec(x_39);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_46);
x_48 = lean_array_fset(x_3, x_4, x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_4, x_49);
lean_dec(x_4);
x_3 = x_48;
x_4 = x_50;
x_9 = x_40;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_54 = x_38;
} else {
 lean_dec_ref(x_38);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract___at_Lean_Meta_GeneralizeTelescope_updateTypes___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_GeneralizeTelescope_updateTypes___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_GeneralizeTelescope_updateTypes___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_GeneralizeTelescope_updateTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withLocalDeclD___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_16 = l_Lean_Meta_GeneralizeTelescope_updateTypes___main(x_2, x_8, x_3, x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_nat_add(x_4, x_14);
x_20 = lean_array_push(x_5, x_8);
x_21 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg(x_6, x_7, x_17, x_15, x_19, x_20, x_9, x_10, x_11, x_12, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create telescope generalizing ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_6(x_2, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
if (x_18 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_16, 0);
lean_inc(x_51);
x_52 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_51, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_17);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_4, x_55);
lean_dec(x_4);
x_57 = lean_array_push(x_6, x_16);
x_4 = x_56;
x_6 = x_57;
x_11 = x_54;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
lean_inc(x_5);
lean_inc(x_1);
x_60 = l_Lean_Name_appendIndexAfter(x_1, x_5);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_61, 0, x_4);
lean_closure_set(x_61, 1, x_16);
lean_closure_set(x_61, 2, x_3);
lean_closure_set(x_61, 3, x_5);
lean_closure_set(x_61, 4, x_6);
lean_closure_set(x_61, 5, x_1);
lean_closure_set(x_61, 6, x_2);
x_62 = 0;
x_63 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_60, x_62, x_17, x_61, x_7, x_8, x_9, x_10, x_59);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_68; 
x_68 = lean_box(0);
x_19 = x_68;
goto block_50;
}
}
else
{
lean_object* x_69; 
x_69 = lean_box(0);
x_19 = x_69;
goto block_50;
}
block_50:
{
lean_dec(x_19);
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Name_appendIndexAfter(x_1, x_5);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_16);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_6);
lean_closure_set(x_21, 5, x_1);
lean_closure_set(x_21, 6, x_2);
x_22 = 0;
x_23 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_20, x_22, x_17, x_21, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_24 = l_Lean_Meta_isTypeCorrect(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = x_3;
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_umapMAux___main___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___spec__2(x_29, x_28);
x_31 = x_30;
x_32 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_33 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_31, x_29, x_32);
lean_dec(x_31);
x_34 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_throwError___at_Lean_mkWHNFRef___spec__1___rarg(x_35, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Name_appendIndexAfter(x_1, x_5);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_43, 0, x_4);
lean_closure_set(x_43, 1, x_16);
lean_closure_set(x_43, 2, x_3);
lean_closure_set(x_43, 3, x_5);
lean_closure_set(x_43, 4, x_6);
lean_closure_set(x_43, 5, x_1);
lean_closure_set(x_43, 6, x_2);
x_44 = 0;
x_45 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_42, x_44, x_17, x_43, x_7, x_8, x_9, x_10, x_41);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_generalizeTelescope___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = x_2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_2, x_1, x_13);
x_15 = x_12;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_instantiateMVars___at_Lean_instantiateLocalDeclMVars___spec__1(x_17, x_3, x_4, x_5, x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = x_23;
x_27 = lean_array_fset(x_14, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Meta_generalizeTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_generalizeTelescope___spec__1), 7, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = x_11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_5(x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Array_empty___closed__1;
x_18 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg(x_2, x_3, x_14, x_10, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_generalizeTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTelescope___rarg), 8, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_GeneralizeTelescope(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__1);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__2);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___main___rarg___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
