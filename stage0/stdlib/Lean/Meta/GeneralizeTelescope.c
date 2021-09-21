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
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4;
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_generalizeTelescope___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_Lean_Meta_kabstract(x_16, x_1, x_17, x_5, x_6, x_7, x_8, x_9);
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
x_38 = l_Lean_Meta_kabstract(x_36, x_1, x_37, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_GeneralizeTelescope_updateTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_14 = l_Lean_Meta_GeneralizeTelescope_updateTypes(x_2, x_6, x_3, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_4, x_6);
x_18 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(x_5, x_15, x_13, x_17, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_7);
x_13 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2;
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_13, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__1), 11, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
x_18 = 0;
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_15, x_18, x_6, x_17, x_8, x_9, x_10, x_11, x_16);
return x_19;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create telescope generalizing ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_6(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_inc(x_5);
x_18 = l_Lean_Meta_getLocalDecl(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_array_push(x_4, x_14);
x_3 = x_22;
x_4 = x_23;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_LocalDecl_userName(x_19);
lean_dec(x_19);
x_27 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_26, x_7, x_8, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__1), 11, 5);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_14);
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_1);
x_31 = 0;
x_32 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_28, x_31, x_16, x_30, x_5, x_6, x_7, x_8, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_38 = l_Lean_Meta_isTypeCorrect(x_37, x_5, x_6, x_7, x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_43 = 0;
x_44 = x_2;
x_45 = l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2(x_42, x_43, x_44);
x_46 = x_45;
x_47 = lean_array_to_list(lean_box(0), x_46);
x_48 = lean_box(0);
x_49 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_47, x_48);
x_50 = l_Lean_MessageData_ofList(x_49);
lean_dec(x_49);
x_51 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_54, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_box(0);
x_62 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2(x_3, x_14, x_2, x_4, x_1, x_37, x_61, x_5, x_6, x_7, x_8, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_dec(x_13);
x_65 = lean_box(0);
x_66 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2(x_3, x_14, x_2, x_4, x_1, x_64, x_65, x_5, x_6, x_7, x_8, x_9);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_67);
x_68 = l_Lean_Meta_isTypeCorrect(x_67, x_5, x_6, x_7, x_8, x_9);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_67);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_73 = 0;
x_74 = x_2;
x_75 = l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2(x_72, x_73, x_74);
x_76 = x_75;
x_77 = lean_array_to_list(lean_box(0), x_76);
x_78 = lean_box(0);
x_79 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_77, x_78);
x_80 = l_Lean_MessageData_ofList(x_79);
lean_dec(x_79);
x_81 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_84, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
x_90 = lean_ctor_get(x_68, 1);
lean_inc(x_90);
lean_dec(x_68);
x_91 = lean_box(0);
x_92 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2(x_3, x_14, x_2, x_4, x_1, x_67, x_91, x_5, x_6, x_7, x_8, x_90);
return x_92;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_instantiateMVars(x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
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
x_24 = 1;
x_25 = x_2 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_14, x_2, x_26);
x_2 = x_25;
x_3 = x_27;
x_8 = x_21;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeTelescope___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = x_1;
x_11 = lean_box_usize(x_9);
x_12 = l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = x_13;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_5(x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Meta_generalizeTelescope___rarg___closed__1;
x_20 = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg(x_2, x_16, x_18, x_19, x_3, x_4, x_5, x_6, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTelescope___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_generalizeTelescope___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeTelescope(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__1);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___lambda__2___closed__2);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__1);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__2);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__3);
l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4 = _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___rarg___closed__4);
l_Lean_Meta_generalizeTelescope___rarg___closed__1 = _init_l_Lean_Meta_generalizeTelescope___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeTelescope___rarg___closed__1);
l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1 = _init_l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_generalizeTelescope___rarg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
