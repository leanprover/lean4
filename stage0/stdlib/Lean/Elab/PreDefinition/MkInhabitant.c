// Lean compiler output
// Module: Lean.Elab.PreDefinition.MkInhabitant
// Imports: Init Lean.Meta.AppBuilder
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
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkInhabitantFor___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Elab_mkInhabitantFor___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkInhabitantFor___closed__3;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkInhabitantFor___closed__2;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
if (x_2 == 0)
{
lean_object* x_18; 
lean_inc(x_5);
x_18 = l_Lean_Meta_mkDefault(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_8 = x_26;
x_9 = x_27;
goto block_17;
}
}
else
{
lean_object* x_28; 
lean_inc(x_5);
x_28 = l_Lean_Meta_mkOfNonempty(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_8 = x_36;
x_9 = x_37;
goto block_17;
}
}
block_17:
{
uint8_t x_10; 
x_10 = l_Lean_Exception_isRuntime(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
lean_dec(x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l_Lean_Meta_isExprDefEq(x_16, x_1, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
lean_inc(x_2);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_14);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_2, x_12, x_1, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_16 = l_Lean_instInhabitedExpr;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkForallFVars(x_19, x_4, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_26 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_24, x_2, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_3 = x_13;
x_4 = x_24;
x_9 = x_28;
goto _start;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_24);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = l_Array_toSubarray___rarg(x_1, x_10, x_13);
x_34 = l_Array_ofSubarray___rarg(x_33);
x_35 = l_Lean_Meta_mkLambdaFVars(x_34, x_32, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_27, 0, x_37);
lean_ctor_set(x_35, 0, x_27);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_27, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_27);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = l_Array_toSubarray___rarg(x_1, x_10, x_13);
x_47 = l_Array_ofSubarray___rarg(x_46);
x_48 = l_Lean_Meta_mkLambdaFVars(x_47, x_45, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
return x_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_23);
if (x_62 == 0)
{
return x_23;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_23, 0);
x_64 = lean_ctor_get(x_23, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_23);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; 
x_66 = lean_array_fget(x_1, x_13);
x_67 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1;
x_68 = lean_array_push(x_67, x_66);
x_69 = 0;
x_70 = 1;
x_71 = 1;
x_72 = l_Lean_Meta_mkForallFVars(x_68, x_4, x_69, x_70, x_71, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_73);
x_75 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_73, x_2, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_3 = x_13;
x_4 = x_73;
x_9 = x_77;
goto _start;
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = l_Array_toSubarray___rarg(x_1, x_10, x_13);
x_83 = l_Array_ofSubarray___rarg(x_82);
x_84 = l_Lean_Meta_mkLambdaFVars(x_83, x_81, x_69, x_70, x_71, x_5, x_6, x_7, x_8, x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_76, 0, x_86);
lean_ctor_set(x_84, 0, x_76);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_76, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_free_object(x_76);
x_90 = !lean_is_exclusive(x_84);
if (x_90 == 0)
{
return x_84;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_84);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_76, 0);
lean_inc(x_94);
lean_dec(x_76);
x_95 = l_Array_toSubarray___rarg(x_1, x_10, x_13);
x_96 = l_Array_ofSubarray___rarg(x_95);
x_97 = l_Lean_Meta_mkLambdaFVars(x_96, x_94, x_69, x_70, x_71, x_5, x_6, x_7, x_8, x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_73);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_75);
if (x_107 == 0)
{
return x_75;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_75, 0);
x_109 = lean_ctor_get(x_75, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_75);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_72);
if (x_111 == 0)
{
return x_72;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_72, 0);
x_113 = lean_ctor_get(x_72, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_72);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_3);
lean_dec(x_1);
x_115 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_115;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop(x_1, x_3, x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to compile partial definition '", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkInhabitantFor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', failed to show that type is inhabited and non empty", 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkInhabitantFor___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_98; lean_object* x_99; 
x_98 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_3, x_98, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_102 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f(x_2, x_3, x_98, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
x_9 = x_108;
x_10 = x_107;
goto block_97;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
x_9 = x_106;
x_10 = x_109;
goto block_97;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_9 = x_112;
x_10 = x_109;
goto block_97;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_105);
if (x_113 == 0)
{
return x_105;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_105, 0);
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_105);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_102, 1);
lean_inc(x_117);
lean_dec(x_102);
x_118 = !lean_is_exclusive(x_103);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_103, 0);
x_120 = 1;
x_121 = 1;
lean_inc(x_2);
x_122 = l_Lean_Meta_mkLambdaFVars(x_2, x_119, x_98, x_120, x_121, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_ctor_set(x_103, 0, x_123);
x_9 = x_103;
x_10 = x_124;
goto block_97;
}
else
{
uint8_t x_125; 
lean_free_object(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_103, 0);
lean_inc(x_129);
lean_dec(x_103);
x_130 = 1;
x_131 = 1;
lean_inc(x_2);
x_132 = l_Lean_Meta_mkLambdaFVars(x_2, x_129, x_98, x_130, x_131, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_133);
x_9 = x_135;
x_10 = x_134;
goto block_97;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
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
uint8_t x_140; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_102);
if (x_140 == 0)
{
return x_102;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_102, 0);
x_142 = lean_ctor_get(x_102, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_102);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_99, 1);
lean_inc(x_144);
lean_dec(x_99);
x_145 = !lean_is_exclusive(x_100);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_100, 0);
x_147 = 1;
x_148 = 1;
lean_inc(x_2);
x_149 = l_Lean_Meta_mkLambdaFVars(x_2, x_146, x_98, x_147, x_148, x_4, x_5, x_6, x_7, x_144);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_ctor_set(x_100, 0, x_150);
x_9 = x_100;
x_10 = x_151;
goto block_97;
}
else
{
uint8_t x_152; 
lean_free_object(x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_149);
if (x_152 == 0)
{
return x_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_149, 0);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_149);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_100, 0);
lean_inc(x_156);
lean_dec(x_100);
x_157 = 1;
x_158 = 1;
lean_inc(x_2);
x_159 = l_Lean_Meta_mkLambdaFVars(x_2, x_156, x_98, x_157, x_158, x_4, x_5, x_6, x_7, x_144);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_160);
x_9 = x_162;
x_10 = x_161;
goto block_97;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_99);
if (x_167 == 0)
{
return x_99;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_99, 0);
x_169 = lean_ctor_get(x_99, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_99);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
block_97:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_22; lean_object* x_23; 
x_22 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(x_3, x_22, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f(x_2, x_3, x_22, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_11 = x_32;
x_12 = x_31;
goto block_21;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
x_11 = x_30;
x_12 = x_33;
goto block_21;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_11 = x_36;
x_12 = x_33;
goto block_21;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_3);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = 0;
x_45 = 1;
x_46 = l_Lean_Meta_mkLambdaFVars(x_2, x_43, x_44, x_22, x_45, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_ctor_set(x_27, 0, x_47);
x_11 = x_27;
x_12 = x_48;
goto block_21;
}
else
{
uint8_t x_49; 
lean_free_object(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_27, 0);
lean_inc(x_53);
lean_dec(x_27);
x_54 = 0;
x_55 = 1;
x_56 = l_Lean_Meta_mkLambdaFVars(x_2, x_53, x_54, x_22, x_55, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_11 = x_59;
x_12 = x_58;
goto block_21;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_3);
x_68 = lean_ctor_get(x_23, 1);
lean_inc(x_68);
lean_dec(x_23);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = 0;
x_72 = 1;
x_73 = l_Lean_Meta_mkLambdaFVars(x_2, x_70, x_71, x_22, x_72, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_ctor_set(x_24, 0, x_74);
x_11 = x_24;
x_12 = x_75;
goto block_21;
}
else
{
uint8_t x_76; 
lean_free_object(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_24, 0);
lean_inc(x_80);
lean_dec(x_24);
x_81 = 0;
x_82 = 1;
x_83 = l_Lean_Meta_mkLambdaFVars(x_2, x_80, x_81, x_22, x_82, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_84);
x_11 = x_86;
x_12 = x_85;
goto block_21;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_23);
if (x_91 == 0)
{
return x_23;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_23, 0);
x_93 = lean_ctor_get(x_23, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_23);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_21:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MessageData_ofName(x_1);
x_14 = l_Lean_Elab_mkInhabitantFor___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_mkInhabitantFor___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_17, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_9, 0);
lean_inc(x_95);
lean_dec(x_9);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_10);
return x_96;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1 = _init_l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___closed__1);
l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1 = _init_l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___closed__1);
l_Lean_Elab_mkInhabitantFor___closed__1 = _init_l_Lean_Elab_mkInhabitantFor___closed__1();
lean_mark_persistent(l_Lean_Elab_mkInhabitantFor___closed__1);
l_Lean_Elab_mkInhabitantFor___closed__2 = _init_l_Lean_Elab_mkInhabitantFor___closed__2();
lean_mark_persistent(l_Lean_Elab_mkInhabitantFor___closed__2);
l_Lean_Elab_mkInhabitantFor___closed__3 = _init_l_Lean_Elab_mkInhabitantFor___closed__3();
lean_mark_persistent(l_Lean_Elab_mkInhabitantFor___closed__3);
l_Lean_Elab_mkInhabitantFor___closed__4 = _init_l_Lean_Elab_mkInhabitantFor___closed__4();
lean_mark_persistent(l_Lean_Elab_mkInhabitantFor___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
