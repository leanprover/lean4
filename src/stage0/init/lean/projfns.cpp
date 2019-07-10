// Lean compiler output
// Module: init.lean.projfns
// Imports: init.lean.environment
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_mkProjectionFnInfoExtension___closed__5;
obj* l_Lean_projectionFnInfoExt___elambda__3(obj*, obj*);
obj* l_Lean_mkProjectionFnInfoExtension___closed__1;
obj* l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_mkProjectionFnInfoExtension___closed__4;
obj* l_Lean_mkProjectionFnInfoExtension___lambda__2___boxed(obj*);
obj* l_Lean_projectionFnInfoExt___elambda__1___boxed(obj*);
obj* l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2(obj*, obj*, obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(obj*, obj*, obj*);
obj* l_Lean_SimplePersistentEnvExtension_getState___rarg(obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_Lean_mkProjectionFnInfoExtension___closed__2;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_projectionFnInfoExt___closed__3;
obj* l_Lean_projectionFnInfoExt___closed__2;
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___elambda__3___boxed(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___elambda__4___closed__1;
obj* l_Array_swap(obj*, obj*, obj*, obj*);
obj* l_Lean_projectionFnInfoExt___elambda__4(obj*);
obj* l_Lean_mkProjectionFnInfoExtension___lambda__3(obj*);
obj* l_Lean_projectionFnInfoExt___elambda__2___boxed(obj*);
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkProjectionFnInfoExtension___lambda__2(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
uint8 l_Lean_Environment_isProjectionFn(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___closed__1;
obj* l_Lean_registerSimplePersistentEnvExtension___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
obj* l_Lean_ProjectionFunctionInfo_inhabited___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_projectionFnInfoExt___elambda__4___boxed(obj*);
obj* l_Lean_mkProjectionFnInfoExtension___lambda__1(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
obj* l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_addProjectionFnInfo___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_projectionFnInfoExt___closed__5;
namespace lean {
obj* add_projection_info_core(obj*, obj*, obj*, obj*, obj*, uint8);
}
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___closed__6;
namespace lean {
obj* get_projection_info_core(obj*, obj*);
}
obj* l_Lean_projectionFnInfoExt___closed__7;
obj* l_Array_size(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkProjectionFnInfoExtension(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Lean_projectionFnInfoExt;
obj* l_Lean_Environment_isProjectionFn___boxed(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___closed__4;
obj* l_Lean_projectionFnInfoExt___elambda__2(obj*);
obj* l_Lean_mkProjectionFnInfoExtension___closed__3;
obj* l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_ProjectionFunctionInfo_inhabited;
obj* l_Lean_mkProjectionFnInfoExtension___closed__6;
obj* l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1(obj*, obj*);
obj* l_Lean_projectionFnInfoExt___elambda__1(obj*);
obj* _init_l_Lean_ProjectionFunctionInfo_inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = 0;
x_4 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
obj* _init_l_Lean_ProjectionFunctionInfo_inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ProjectionFunctionInfo_inhabited___closed__1;
return x_1;
}
}
obj* _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Inhabited;
x_2 = l_Lean_ProjectionFunctionInfo_inhabited;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_5);
x_7 = lean::array_swap(x_3, x_4, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
x_10 = lean::array_get(x_9, x_3, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::array_swap(x_3, x_4, x_5);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_20 = lean::nat_add(x_5, x_18);
lean::dec(x_5);
x_3 = x_17;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_5 = lean::nat_add(x_2, x_3);
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
x_57 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
x_58 = lean::array_get(x_57, x_1, x_7);
x_59 = lean::array_get(x_57, x_1, x_2);
x_60 = lean::cnstr_get(x_58, 0);
lean::inc(x_60);
lean::dec(x_58);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_62 = l_Lean_Name_quickLt(x_60, x_61);
lean::dec(x_61);
lean::dec(x_60);
if (x_62 == 0)
{
x_8 = x_1;
goto block_56;
}
else
{
obj* x_63; 
x_63 = lean::array_swap(x_1, x_2, x_7);
x_8 = x_63;
goto block_56;
}
block_56:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
x_10 = lean::array_get(x_9, x_8, x_3);
x_11 = lean::array_get(x_9, x_8, x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::array_get(x_9, x_8, x_7);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l_Lean_Name_quickLt(x_16, x_12);
lean::dec(x_12);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_18 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(x_3, x_10, x_8, x_2, x_2);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
x_21 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_20, x_2, x_19);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_19);
x_1 = x_21;
x_2 = x_23;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
x_25 = lean::array_swap(x_8, x_7, x_3);
lean::dec(x_7);
x_26 = lean::array_get(x_9, x_25, x_3);
lean::inc(x_2, 2);
x_27 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(x_3, x_26, x_25, x_2, x_2);
lean::dec(x_26);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_29, x_2, x_28);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_28, x_31);
lean::dec(x_28);
x_1 = x_30;
x_2 = x_32;
goto _start;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; 
lean::dec(x_12);
lean::dec(x_10);
x_34 = lean::array_swap(x_8, x_2, x_3);
x_35 = lean::array_get(x_9, x_34, x_7);
x_36 = lean::array_get(x_9, x_34, x_3);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::dec(x_35);
x_38 = lean::cnstr_get(x_36, 0);
lean::inc(x_38);
x_39 = l_Lean_Name_quickLt(x_37, x_38);
lean::dec(x_38);
lean::dec(x_37);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_40 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(x_3, x_36, x_34, x_2, x_2);
lean::dec(x_36);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_42, x_2, x_41);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_add(x_41, x_44);
lean::dec(x_41);
x_1 = x_43;
x_2 = x_45;
goto _start;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_36);
x_47 = lean::array_swap(x_34, x_7, x_3);
lean::dec(x_7);
x_48 = lean::array_get(x_9, x_47, x_3);
lean::inc(x_2, 2);
x_49 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(x_3, x_48, x_47, x_2, x_2);
lean::dec(x_48);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
lean::dec(x_49);
x_52 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_51, x_2, x_50);
x_53 = lean::mk_nat_obj(1u);
x_54 = lean::nat_add(x_50, x_53);
lean::dec(x_50);
x_1 = x_52;
x_2 = x_54;
goto _start;
}
}
}
}
}
}
obj* l_Lean_mkProjectionFnInfoExtension___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
obj* l_Lean_mkProjectionFnInfoExtension___lambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_mkProjectionFnInfoExtension___lambda__3(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean::mk_empty_array(x_2);
lean::dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
x_5 = lean::array_get_size(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_4, x_8, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("projinfo");
return x_1;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkProjectionFnInfoExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProjectionFnInfoExtension___lambda__1), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProjectionFnInfoExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProjectionFnInfoExtension___lambda__3), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_mkProjectionFnInfoExtension___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_mkProjectionFnInfoExtension___closed__2;
x_2 = l_Lean_mkProjectionFnInfoExtension___closed__3;
x_3 = l_Lean_mkProjectionFnInfoExtension___closed__4;
x_4 = l_Lean_mkProjectionFnInfoExtension___closed__5;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
return x_5;
}
}
obj* l_Lean_mkProjectionFnInfoExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkProjectionFnInfoExtension___closed__6;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_mkProjectionFnInfoExtension___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_mkProjectionFnInfoExtension___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_mkProjectionFnInfoExtension___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__3(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_Lean_projectionFnInfoExt___elambda__4___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__4___closed__1;
return x_2;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_projectionFnInfoExt___elambda__4___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_projectionFnInfoExt___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_projectionFnInfoExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_projectionFnInfoExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_projectionFnInfoExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_projectionFnInfoExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_projectionFnInfoExt___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_projectionFnInfoExt___closed__2;
x_2 = lean::box(0);
x_3 = l_Lean_projectionFnInfoExt___closed__3;
x_4 = l_Lean_projectionFnInfoExt___closed__4;
x_5 = l_Lean_projectionFnInfoExt___closed__5;
x_6 = l_Lean_projectionFnInfoExt___closed__6;
x_7 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_4);
lean::cnstr_set(x_7, 4, x_5);
lean::cnstr_set(x_7, 5, x_6);
return x_7;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_projectionFnInfoExt___elambda__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_projectionFnInfoExt___elambda__4___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__4(x_1);
lean::dec(x_1);
return x_2;
}
}
namespace lean {
obj* add_projection_info_core(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_projectionFnInfoExt;
x_10 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_9, x_1, x_8);
return x_10;
}
}
}
obj* l_Lean_addProjectionFnInfo___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = lean::add_projection_info_core(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::nat_add(x_3, x_4);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
x_10 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
x_11 = lean::array_get(x_10, x_1, x_9);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8 x_15; 
lean::dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean::dec(x_12);
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_11);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_9, x_19);
lean::dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_3);
x_22 = lean::box(0);
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_3);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_9, x_23);
lean::dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
namespace lean {
obj* get_projection_info_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_projectionFnInfoExt;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_4, x_1);
lean::dec(x_1);
x_6 = l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_8 = l_Lean_projectionFnInfoExt;
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_8, x_1, x_7);
lean::dec(x_7);
lean::dec(x_1);
x_10 = l_Lean_ProjectionFunctionInfo_inhabited___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::array_get_size(x_9);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_12, x_13);
lean::dec(x_12);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2(x_9, x_11, x_15, x_14);
lean::dec(x_11);
lean::dec(x_9);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; 
x_17 = lean::box(0);
return x_17;
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_16);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_16, 0);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
lean::cnstr_set(x_16, 0, x_20);
return x_16;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Environment_getProjectionFnInfo___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_Environment_getProjectionFnInfo___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
uint8 l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_4);
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::nat_add(x_3, x_4);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
x_10 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1;
x_11 = lean::array_get(x_10, x_1, x_9);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8 x_15; 
lean::dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean::dec(x_12);
if (x_15 == 0)
{
uint8 x_16; 
lean::dec(x_9);
lean::dec(x_3);
x_16 = 1;
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_9, x_19);
lean::dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
uint8 x_22; 
lean::dec(x_9);
lean::dec(x_3);
x_22 = 0;
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_12);
lean::dec(x_3);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_9, x_23);
lean::dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
uint8 l_Lean_Environment_isProjectionFn(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_Lean_projectionFnInfoExt;
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_4, x_1);
x_6 = l_Lean_NameMap_contains___rarg(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_8 = l_Lean_projectionFnInfoExt;
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_8, x_1, x_7);
lean::dec(x_7);
x_10 = l_Lean_ProjectionFunctionInfo_inhabited___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::array_get_size(x_9);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_12, x_13);
lean::dec(x_12);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1(x_9, x_11, x_15, x_14);
lean::dec(x_11);
lean::dec(x_9);
return x_16;
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Array_binSearchAux___main___at_Lean_Environment_isProjectionFn___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_Environment_isProjectionFn___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Environment_isProjectionFn(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_projfns(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
l_Lean_ProjectionFunctionInfo_inhabited___closed__1 = _init_l_Lean_ProjectionFunctionInfo_inhabited___closed__1();
lean::mark_persistent(l_Lean_ProjectionFunctionInfo_inhabited___closed__1);
l_Lean_ProjectionFunctionInfo_inhabited = _init_l_Lean_ProjectionFunctionInfo_inhabited();
lean::mark_persistent(l_Lean_ProjectionFunctionInfo_inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ProjectionFunctionInfo"), "inhabited"), l_Lean_ProjectionFunctionInfo_inhabited);
l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1 = _init_l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1();
lean::mark_persistent(l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProjectionFnInfoExtension___spec__2___closed__1);
l_Lean_mkProjectionFnInfoExtension___closed__1 = _init_l_Lean_mkProjectionFnInfoExtension___closed__1();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__1);
l_Lean_mkProjectionFnInfoExtension___closed__2 = _init_l_Lean_mkProjectionFnInfoExtension___closed__2();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__2);
l_Lean_mkProjectionFnInfoExtension___closed__3 = _init_l_Lean_mkProjectionFnInfoExtension___closed__3();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__3);
l_Lean_mkProjectionFnInfoExtension___closed__4 = _init_l_Lean_mkProjectionFnInfoExtension___closed__4();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__4);
l_Lean_mkProjectionFnInfoExtension___closed__5 = _init_l_Lean_mkProjectionFnInfoExtension___closed__5();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__5);
l_Lean_mkProjectionFnInfoExtension___closed__6 = _init_l_Lean_mkProjectionFnInfoExtension___closed__6();
lean::mark_persistent(l_Lean_mkProjectionFnInfoExtension___closed__6);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkProjectionFnInfoExtension"), 1, l_Lean_mkProjectionFnInfoExtension);
l_Lean_projectionFnInfoExt___elambda__4___closed__1 = _init_l_Lean_projectionFnInfoExt___elambda__4___closed__1();
lean::mark_persistent(l_Lean_projectionFnInfoExt___elambda__4___closed__1);
l_Lean_projectionFnInfoExt___closed__1 = _init_l_Lean_projectionFnInfoExt___closed__1();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__1);
l_Lean_projectionFnInfoExt___closed__2 = _init_l_Lean_projectionFnInfoExt___closed__2();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__2);
l_Lean_projectionFnInfoExt___closed__3 = _init_l_Lean_projectionFnInfoExt___closed__3();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__3);
l_Lean_projectionFnInfoExt___closed__4 = _init_l_Lean_projectionFnInfoExt___closed__4();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__4);
l_Lean_projectionFnInfoExt___closed__5 = _init_l_Lean_projectionFnInfoExt___closed__5();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__5);
l_Lean_projectionFnInfoExt___closed__6 = _init_l_Lean_projectionFnInfoExt___closed__6();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__6);
l_Lean_projectionFnInfoExt___closed__7 = _init_l_Lean_projectionFnInfoExt___closed__7();
lean::mark_persistent(l_Lean_projectionFnInfoExt___closed__7);
w = l_Lean_mkProjectionFnInfoExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_projectionFnInfoExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_projectionFnInfoExt);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "projectionFnInfoExt"), l_Lean_projectionFnInfoExt);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "addProjectionFnInfo"), 6, l_Lean_addProjectionFnInfo___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "getProjectionFnInfo"), 2, lean::get_projection_info_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Environment"), "isProjectionFn"), 2, l_Lean_Environment_isProjectionFn___boxed);
return w;
}
