// Lean compiler output
// Module: Init.Lean.Structure
// Imports: Init.Lean.Environment Init.Lean.ProjFns
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_getStructureCtor___closed__1;
lean_object* l_Lean_getStructureCtor___closed__2;
lean_object* l___private_Init_Lean_Structure_4__hasProjFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Structure_4__hasProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor___closed__4;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_contains___at_Lean_findField_x3f___main___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_isStructureLike___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor___closed__5;
lean_object* l_Lean_getStructureCtor___closed__3;
lean_object* l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructureAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Structure_4__hasProjFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkInternalSubobjectFieldName(lean_object*);
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1;
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* l_Lean_isStructure___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ConstructorVal_inhabited;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_deinternalizeFieldName(lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructureAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructureAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_4__hasProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInternalSubobjectFieldName___boxed(lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructureAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec(x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_6);
x_13 = 0;
return x_13;
}
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 0;
return x_14;
}
}
}
}
lean_object* l_Lean_isStructureLike___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isStructureLike(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_mkInternalSubobjectFieldName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
x_3 = l_Lean_Name_appendBefore(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_string_length(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_2, x_4);
x_8 = 95;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
lean_object* l_Lean_isInternalSubobjectFieldName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isInternalSubobjectFieldName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_deinternalizeFieldName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_length(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_3, x_5);
x_8 = 95;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_String_drop(x_3, x_10);
lean_dec(x_3);
x_12 = lean_name_mk_string(x_2, x_11);
return x_12;
}
}
}
else
{
return x_1;
}
}
}
lean_object* _init_l_Lean_getStructureCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Structure");
return x_1;
}
}
lean_object* _init_l_Lean_getStructureCtor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure expected");
return x_1;
}
}
lean_object* _init_l_Lean_getStructureCtor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_getStructureCtor___closed__1;
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_unsigned_to_nat(7u);
x_4 = l_Lean_getStructureCtor___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_getStructureCtor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed environment");
return x_1;
}
}
lean_object* _init_l_Lean_getStructureCtor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_getStructureCtor___closed__1;
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_unsigned_to_nat(9u);
x_4 = l_Lean_getStructureCtor___closed__4;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_getStructureCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = l_Lean_ConstructorVal_inhabited;
x_5 = l_Lean_getStructureCtor___closed__3;
x_6 = lean_panic_fn(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_1);
x_10 = l_Lean_ConstructorVal_inhabited;
x_11 = l_Lean_getStructureCtor___closed__3;
x_12 = lean_panic_fn(x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_environment_find(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_ConstructorVal_inhabited;
x_18 = l_Lean_getStructureCtor___closed__5;
x_19 = lean_panic_fn(x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 6)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_22 = l_Lean_ConstructorVal_inhabited;
x_23 = l_Lean_getStructureCtor___closed__5;
x_24 = lean_panic_fn(x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_1);
x_25 = l_Lean_ConstructorVal_inhabited;
x_26 = l_Lean_getStructureCtor___closed__3;
x_27 = lean_panic_fn(x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_28 = l_Lean_ConstructorVal_inhabited;
x_29 = l_Lean_getStructureCtor___closed__3;
x_30 = lean_panic_fn(x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_1);
x_31 = l_Lean_ConstructorVal_inhabited;
x_32 = l_Lean_getStructureCtor___closed__3;
x_33 = lean_panic_fn(x_32);
return x_33;
}
}
}
}
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_nat_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_10 = l_Lean_deinternalizeFieldName(x_5);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_9;
x_3 = x_6;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_1__getStructureFieldsAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_1__getStructureFieldsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Structure_1__getStructureFieldsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_1__getStructureFieldsAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_getStructureFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_getStructureCtor(x_1, x_2);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = l___private_Init_Lean_Structure_1__getStructureFieldsAux___main(x_4, x_7, x_6, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* _init_l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed structure");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_getStructureCtor___closed__1;
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(11u);
x_4 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_nat_dec_lt(x_3, x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_name_eq(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2;
x_18 = lean_panic_fn(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_7;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Structure_2__isSubobjectFieldAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_isSubobjectField_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_getStructureCtor(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = l_Lean_Name_appendIndexAfter___closed__1;
x_7 = l_Lean_Name_appendBefore(x_3, x_6);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main(x_5, x_7, x_10, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_isSubobjectField_x3f(x_1, x_2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_push(x_5, x_13);
x_4 = x_11;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Lean_getParentStructures(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_getStructureFields(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_getParentStructures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Lean_findField_x3f___main(x_1, x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_findField_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_getStructureFields(x_1, x_2);
x_5 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_4, x_3);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = l_Lean_getParentStructures(x_1, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3(x_1, x_3, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_findField_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_findField_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findMAux___main___at_Lean_findField_x3f___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_findField_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findField_x3f___main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_findField_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findField_x3f___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_findField_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findField_x3f(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_8);
x_9 = lean_array_push(x_5, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_isSubobjectField_x3f(x_1, x_2, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
x_4 = x_12;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_1);
x_15 = l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main(x_1, x_14, x_9);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_getStructureFields(x_1, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1(x_1, x_2, x_4, x_5, x_3);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getStructureFieldsFlattened(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_empty___closed__1;
x_4 = l___private_Init_Lean_Structure_3__getStructureFieldsFlattenedAux___main(x_1, x_2, x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Structure_4__hasProjFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_4);
x_9 = l_Lean_deinternalizeFieldName(x_6);
x_10 = l_Lean_Name_append___main(x_2, x_9);
x_11 = l_Lean_Environment_isProjectionFn(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_7;
goto _start;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
lean_object* l___private_Init_Lean_Structure_4__hasProjFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Lean_Structure_4__hasProjFn___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
uint8_t l___private_Init_Lean_Structure_4__hasProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Init_Lean_Structure_4__hasProjFn___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Structure_4__hasProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Lean_Structure_4__hasProjFn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
uint8_t l_Lean_isStructure(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_isStructureLike(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_getStructureCtor(x_1, x_2);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Lean_Structure_4__hasProjFn___main(x_1, x_2, x_6, x_9, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
lean_object* l_Lean_isStructure___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isStructure(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_5, x_6);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_isSubobjectField_x3f(x_1, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Name_append___main(x_3, x_10);
lean_inc(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
lean_inc(x_1);
x_18 = l_Lean_getPathToBaseStructureAux___main(x_1, x_2, x_15, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
}
}
}
lean_object* l_Lean_getPathToBaseStructureAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_name_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_getStructureFields(x_1, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1(x_1, x_2, x_3, x_4, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_List_reverse___rarg(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
lean_object* l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findMAux___main___at_Lean_getPathToBaseStructureAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_getPathToBaseStructureAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getPathToBaseStructureAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_getPathToBaseStructureAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getPathToBaseStructureAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_getPathToBaseStructureAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getPathToBaseStructureAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_getPathToBaseStructureAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_getPathToBaseStructure_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getPathToBaseStructure_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_ProjFns(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Structure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_getStructureCtor___closed__1 = _init_l_Lean_getStructureCtor___closed__1();
lean_mark_persistent(l_Lean_getStructureCtor___closed__1);
l_Lean_getStructureCtor___closed__2 = _init_l_Lean_getStructureCtor___closed__2();
lean_mark_persistent(l_Lean_getStructureCtor___closed__2);
l_Lean_getStructureCtor___closed__3 = _init_l_Lean_getStructureCtor___closed__3();
lean_mark_persistent(l_Lean_getStructureCtor___closed__3);
l_Lean_getStructureCtor___closed__4 = _init_l_Lean_getStructureCtor___closed__4();
lean_mark_persistent(l_Lean_getStructureCtor___closed__4);
l_Lean_getStructureCtor___closed__5 = _init_l_Lean_getStructureCtor___closed__5();
lean_mark_persistent(l_Lean_getStructureCtor___closed__5);
l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1 = _init_l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__1);
l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2 = _init_l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Structure_2__isSubobjectFieldAux___main___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
