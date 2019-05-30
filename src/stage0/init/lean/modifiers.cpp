// Lean compiler output
// Module: init.lean.modifiers
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
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_mkProtectedExtension___lambda__2(obj*);
obj* l_Thunk_pure(obj*, obj*);
namespace lean {
obj* add_protected_core(obj*, obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1(uint8, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_isProtected___boxed(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_protectedExt___elambda__1(obj*);
extern obj* l___private_init_lean_environment_9__persistentEnvExtensionsRef;
obj* l_Array_swap(obj*, obj*, obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj*, obj*);
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(obj*, obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_Environment_getModuleIdxFor(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_mkProtectedExtension___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_protectedExt;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_push(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(obj*, obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj*, obj*, obj*);
uint8 l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_protectedExt___elambda__2___rarg(obj*, obj*);
obj* l_Lean_protectedExt___elambda__2(uint8);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
namespace lean {
uint8 is_protected_core(obj*, obj*);
}
obj* l_Array_size(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4___boxed(obj*, obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Lean_mkProtectedExtension(obj*);
obj* l_Array_binSearchAux___main___at_Lean_isProtected___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_protectedExt___elambda__2___boxed(obj*);
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = l_Lean_Inhabited;
x_10 = lean::array_get(x_9, x_3, x_5);
x_11 = l_Lean_Name_quickLt(x_10, x_2);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_5, x_12);
lean::dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::array_swap(x_3, x_4, x_5);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_4, x_16);
lean::dec(x_4);
x_18 = lean::nat_add(x_5, x_16);
lean::dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_5 = lean::nat_add(x_2, x_3);
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
x_52 = l_Lean_Inhabited;
x_53 = lean::array_get(x_52, x_1, x_7);
x_54 = lean::array_get(x_52, x_1, x_2);
x_55 = l_Lean_Name_quickLt(x_53, x_54);
lean::dec(x_54);
lean::dec(x_53);
if (x_55 == 0)
{
x_8 = x_1;
goto block_51;
}
else
{
obj* x_56; 
x_56 = lean::array_swap(x_1, x_2, x_7);
x_8 = x_56;
goto block_51;
}
block_51:
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = l_Lean_Inhabited;
x_10 = lean::array_get(x_9, x_8, x_3);
x_11 = lean::array_get(x_9, x_8, x_2);
x_12 = l_Lean_Name_quickLt(x_10, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::array_get(x_9, x_8, x_7);
x_14 = l_Lean_Name_quickLt(x_13, x_10);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_15 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_3, x_10, x_8, x_2, x_2);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
lean::dec(x_15);
x_18 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_17, x_2, x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_16, x_19);
lean::dec(x_16);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
x_22 = lean::array_swap(x_8, x_7, x_3);
lean::dec(x_7);
x_23 = lean::array_get(x_9, x_22, x_3);
lean::inc(x_2, 2);
x_24 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_3, x_23, x_22, x_2, x_2);
lean::dec(x_23);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_24, 1);
lean::inc(x_26);
lean::dec(x_24);
x_27 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_26, x_2, x_25);
x_28 = lean::mk_nat_obj(1u);
x_29 = lean::nat_add(x_25, x_28);
lean::dec(x_25);
x_1 = x_27;
x_2 = x_29;
goto _start;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
lean::dec(x_10);
x_31 = lean::array_swap(x_8, x_2, x_3);
x_32 = lean::array_get(x_9, x_31, x_7);
x_33 = lean::array_get(x_9, x_31, x_3);
x_34 = l_Lean_Name_quickLt(x_32, x_33);
lean::dec(x_32);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_7);
lean::inc(x_2, 2);
x_35 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_3, x_33, x_31, x_2, x_2);
lean::dec(x_33);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
lean::dec(x_35);
x_38 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_37, x_2, x_36);
x_39 = lean::mk_nat_obj(1u);
x_40 = lean::nat_add(x_36, x_39);
lean::dec(x_36);
x_1 = x_38;
x_2 = x_40;
goto _start;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_33);
x_42 = lean::array_swap(x_31, x_7, x_3);
lean::dec(x_7);
x_43 = lean::array_get(x_9, x_42, x_3);
lean::inc(x_2, 2);
x_44 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_3, x_43, x_42, x_2, x_2);
lean::dec(x_43);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
lean::dec(x_44);
x_47 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_46, x_2, x_45);
x_48 = lean::mk_nat_obj(1u);
x_49 = lean::nat_add(x_45, x_48);
lean::dec(x_45);
x_1 = x_47;
x_2 = x_49;
goto _start;
}
}
}
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean::dec(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean::dec(x_3);
return x_10;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 4);
lean::inc(x_7);
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
lean::inc(x_4);
x_9 = lean::thunk_pure(x_4);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_4);
x_12 = l_Array_empty___closed__1;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set(x_13, 2, x_10);
lean::cnstr_set(x_13, 3, x_11);
x_14 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_15 = lean::io_ref_get(x_14, x_2);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(x_1, x_17, x_18);
lean::dec(x_17);
lean::dec(x_1);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::box(0);
lean::cnstr_set(x_15, 0, x_20);
x_21 = l_Lean_registerEnvExtensionUnsafe___rarg(x_13, x_15);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_20);
x_24 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_3);
lean::cnstr_set(x_24, 2, x_5);
lean::cnstr_set(x_24, 3, x_6);
lean::cnstr_set(x_24, 4, x_7);
lean::cnstr_set_scalar(x_24, sizeof(void*)*5, x_8);
x_25 = lean::io_ref_get(x_14, x_21);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
lean::cnstr_set(x_25, 0, x_20);
x_28 = lean::io_ref_reset(x_14, x_25);
if (lean::obj_tag(x_28) == 0)
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_28, 0);
lean::dec(x_30);
lean::cnstr_set(x_28, 0, x_20);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_24);
x_32 = x_24;
x_33 = lean::array_push(x_27, x_32);
x_34 = lean::io_ref_set(x_14, x_33, x_28);
if (lean::obj_tag(x_34) == 0)
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_34);
if (x_35 == 0)
{
obj* x_36; 
x_36 = lean::cnstr_get(x_34, 0);
lean::dec(x_36);
lean::cnstr_set(x_34, 0, x_24);
return x_34;
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_24);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8 x_39; 
lean::dec(x_24);
x_39 = !lean::is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_34, 0);
x_41 = lean::cnstr_get(x_34, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_34);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_28, 1);
lean::inc(x_43);
lean::dec(x_28);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_20);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_24);
x_46 = x_24;
x_47 = lean::array_push(x_27, x_46);
x_48 = lean::io_ref_set(x_14, x_47, x_44);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_50 = x_48;
} else {
 lean::dec_ref(x_48);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_24);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_24);
x_52 = lean::cnstr_get(x_48, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_54 = x_48;
} else {
 lean::dec_ref(x_48);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8 x_56; 
lean::dec(x_27);
lean::dec(x_24);
x_56 = !lean::is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = lean::cnstr_get(x_28, 0);
x_58 = lean::cnstr_get(x_28, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_28);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_25, 0);
x_61 = lean::cnstr_get(x_25, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_25);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_61);
x_63 = lean::io_ref_reset(x_14, x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_65 = x_63;
} else {
 lean::dec_ref(x_63);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_20);
lean::cnstr_set(x_66, 1, x_64);
x_67 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_24);
x_68 = x_24;
x_69 = lean::array_push(x_60, x_68);
x_70 = lean::io_ref_set(x_14, x_69, x_66);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_70, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_72 = x_70;
} else {
 lean::dec_ref(x_70);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_24);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_24);
x_74 = lean::cnstr_get(x_70, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_70, 1);
lean::inc(x_75);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_76 = x_70;
} else {
 lean::dec_ref(x_70);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
return x_77;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_60);
lean::dec(x_24);
x_78 = lean::cnstr_get(x_63, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_63, 1);
lean::inc(x_79);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_80 = x_63;
} else {
 lean::dec_ref(x_63);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8 x_82; 
lean::dec(x_24);
x_82 = !lean::is_exclusive(x_25);
if (x_82 == 0)
{
return x_25;
}
else
{
obj* x_83; obj* x_84; obj* x_85; 
x_83 = lean::cnstr_get(x_25, 0);
x_84 = lean::cnstr_get(x_25, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_25);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_86 = lean::cnstr_get(x_21, 0);
x_87 = lean::cnstr_get(x_21, 1);
lean::inc(x_87);
lean::inc(x_86);
lean::dec(x_21);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_20);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_3);
lean::cnstr_set(x_89, 2, x_5);
lean::cnstr_set(x_89, 3, x_6);
lean::cnstr_set(x_89, 4, x_7);
lean::cnstr_set_scalar(x_89, sizeof(void*)*5, x_8);
x_90 = lean::io_ref_get(x_14, x_88);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 x_93 = x_90;
} else {
 lean::dec_ref(x_90);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_20);
lean::cnstr_set(x_94, 1, x_92);
x_95 = lean::io_ref_reset(x_14, x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_96 = lean::cnstr_get(x_95, 1);
lean::inc(x_96);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_97 = x_95;
} else {
 lean::dec_ref(x_95);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_20);
lean::cnstr_set(x_98, 1, x_96);
x_99 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_89);
x_100 = x_89;
x_101 = lean::array_push(x_91, x_100);
x_102 = lean::io_ref_set(x_14, x_101, x_98);
if (lean::obj_tag(x_102) == 0)
{
obj* x_103; obj* x_104; obj* x_105; 
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_104 = x_102;
} else {
 lean::dec_ref(x_102);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_89);
lean::cnstr_set(x_105, 1, x_103);
return x_105;
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_89);
x_106 = lean::cnstr_get(x_102, 0);
lean::inc(x_106);
x_107 = lean::cnstr_get(x_102, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_108 = x_102;
} else {
 lean::dec_ref(x_102);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
lean::cnstr_set(x_109, 1, x_107);
return x_109;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_91);
lean::dec(x_89);
x_110 = lean::cnstr_get(x_95, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_95, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_112 = x_95;
} else {
 lean::dec_ref(x_95);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_89);
x_114 = lean::cnstr_get(x_90, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_90, 1);
lean::inc(x_115);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 x_116 = x_90;
} else {
 lean::dec_ref(x_90);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
uint8 x_118; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_118 = !lean::is_exclusive(x_21);
if (x_118 == 0)
{
return x_21;
}
else
{
obj* x_119; obj* x_120; obj* x_121; 
x_119 = lean::cnstr_get(x_21, 0);
x_120 = lean::cnstr_get(x_21, 1);
lean::inc(x_120);
lean::inc(x_119);
lean::dec(x_21);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_122 = l_Lean_Name_toString___closed__1;
x_123 = l_Lean_Name_toStringWithSep___main(x_122, x_3);
x_124 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_125 = lean::string_append(x_124, x_123);
lean::dec(x_123);
x_126 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_127 = lean::string_append(x_125, x_126);
lean::cnstr_set_tag(x_15, 1);
lean::cnstr_set(x_15, 0, x_127);
return x_15;
}
}
else
{
obj* x_128; obj* x_129; obj* x_130; uint8 x_131; 
x_128 = lean::cnstr_get(x_15, 0);
x_129 = lean::cnstr_get(x_15, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_15);
x_130 = lean::mk_nat_obj(0u);
x_131 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(x_1, x_128, x_130);
lean::dec(x_128);
lean::dec(x_1);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; 
x_132 = lean::box(0);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_129);
x_134 = l_Lean_registerEnvExtensionUnsafe___rarg(x_13, x_133);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_134, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_137 = x_134;
} else {
 lean::dec_ref(x_134);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_132);
lean::cnstr_set(x_138, 1, x_136);
x_139 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_139, 0, x_135);
lean::cnstr_set(x_139, 1, x_3);
lean::cnstr_set(x_139, 2, x_5);
lean::cnstr_set(x_139, 3, x_6);
lean::cnstr_set(x_139, 4, x_7);
lean::cnstr_set_scalar(x_139, sizeof(void*)*5, x_8);
x_140 = lean::io_ref_get(x_14, x_138);
if (lean::obj_tag(x_140) == 0)
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_142 = lean::cnstr_get(x_140, 1);
lean::inc(x_142);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_143 = x_140;
} else {
 lean::dec_ref(x_140);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_132);
lean::cnstr_set(x_144, 1, x_142);
x_145 = lean::io_ref_reset(x_14, x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_147 = x_145;
} else {
 lean::dec_ref(x_145);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_132);
lean::cnstr_set(x_148, 1, x_146);
x_149 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_139);
x_150 = x_139;
x_151 = lean::array_push(x_141, x_150);
x_152 = lean::io_ref_set(x_14, x_151, x_148);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_154 = x_152;
} else {
 lean::dec_ref(x_152);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_139);
lean::cnstr_set(x_155, 1, x_153);
return x_155;
}
else
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_139);
x_156 = lean::cnstr_get(x_152, 0);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_152, 1);
lean::inc(x_157);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_158 = x_152;
} else {
 lean::dec_ref(x_152);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_157);
return x_159;
}
}
else
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_141);
lean::dec(x_139);
x_160 = lean::cnstr_get(x_145, 0);
lean::inc(x_160);
x_161 = lean::cnstr_get(x_145, 1);
lean::inc(x_161);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_162 = x_145;
} else {
 lean::dec_ref(x_145);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
lean::cnstr_set(x_163, 1, x_161);
return x_163;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_139);
x_164 = lean::cnstr_get(x_140, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_140, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_166 = x_140;
} else {
 lean::dec_ref(x_140);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_164);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
x_168 = lean::cnstr_get(x_134, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_134, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_170 = x_134;
} else {
 lean::dec_ref(x_134);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_172 = l_Lean_Name_toString___closed__1;
x_173 = l_Lean_Name_toStringWithSep___main(x_172, x_3);
x_174 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_175 = lean::string_append(x_174, x_173);
lean::dec(x_173);
x_176 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_177 = lean::string_append(x_175, x_176);
x_178 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_129);
return x_178;
}
}
}
else
{
uint8 x_179; 
lean::dec(x_13);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_179 = !lean::is_exclusive(x_15);
if (x_179 == 0)
{
return x_15;
}
else
{
obj* x_180; obj* x_181; obj* x_182; 
x_180 = lean::cnstr_get(x_15, 0);
x_181 = lean::cnstr_get(x_15, 1);
lean::inc(x_181);
lean::inc(x_180);
lean::dec(x_15);
x_182 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_182, 0, x_180);
lean::cnstr_set(x_182, 1, x_181);
return x_182;
}
}
}
}
obj* l_Lean_mkProtectedExtension___lambda__1(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
if (x_1 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_3, x_4);
return x_5;
}
else
{
lean::dec(x_3);
return x_2;
}
}
}
obj* l_Lean_mkProtectedExtension___lambda__2(obj* x_1) {
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
x_9 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_4, x_8, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* _init_l_Lean_mkProtectedExtension___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; 
x_1 = lean::box(0);
x_2 = lean::mk_string("protected");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProtectedExtension___lambda__1___boxed), 3, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProtectedExtension___lambda__2), 1, 0);
x_7 = 0;
x_8 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_1);
lean::cnstr_set(x_8, 3, x_5);
lean::cnstr_set(x_8, 4, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*5, x_7);
return x_8;
}
}
obj* l_Lean_mkProtectedExtension(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkProtectedExtension___closed__1;
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(x_2, x_1);
return x_3;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Lean_mkProtectedExtension___lambda__1(x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_protectedExt___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean::mk_empty_array(x_2);
lean::dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_protectedExt___elambda__2(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_protectedExt___elambda__2___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_protectedExt___elambda__2___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_protectedExt___elambda__2___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_protectedExt___elambda__2(x_2);
return x_3;
}
}
namespace lean {
obj* add_protected_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
}
uint8 l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_7 = lean::nat_add(x_3, x_4);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
x_10 = l_Lean_Inhabited;
x_11 = lean::array_get(x_10, x_1, x_9);
x_12 = l_Lean_Name_quickLt(x_11, x_2);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_4);
x_13 = l_Lean_Name_quickLt(x_2, x_11);
lean::dec(x_11);
if (x_13 == 0)
{
uint8 x_14; 
lean::dec(x_9);
lean::dec(x_3);
x_14 = 1;
return x_14;
}
else
{
obj* x_15; uint8 x_16; 
x_15 = lean::mk_nat_obj(0u);
x_16 = lean::nat_dec_eq(x_9, x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_9, x_17);
lean::dec(x_9);
x_4 = x_18;
goto _start;
}
else
{
uint8 x_20; 
lean::dec(x_9);
lean::dec(x_3);
x_20 = 0;
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; uint8 x_23; 
lean::dec(x_11);
lean::dec(x_3);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_9, x_21);
lean::dec(x_9);
x_3 = x_22;
goto _start;
}
}
}
}
namespace lean {
uint8 is_protected_core(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_Lean_protectedExt;
x_5 = l_Lean_PersistentEnvExtension_getState___rarg(x_4, x_1);
lean::dec(x_1);
x_6 = l_Lean_NameSet_contains(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_8 = l_Lean_protectedExt;
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_8, x_1, x_7);
lean::dec(x_7);
lean::dec(x_1);
x_10 = lean::array_get_size(x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_10, x_11);
lean::dec(x_10);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(x_9, x_2, x_13, x_12);
lean::dec(x_2);
lean::dec(x_9);
return x_14;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_isProtected___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_isProtected___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::is_protected_core(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_lean_environment(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_modifiers(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
l_Lean_mkProtectedExtension___closed__1 = _init_l_Lean_mkProtectedExtension___closed__1();
lean::mark_persistent(l_Lean_mkProtectedExtension___closed__1);
w = l_Lean_mkProtectedExtension(w);
if (io_result_is_error(w)) return w;
l_Lean_protectedExt = io_result_get_value(w);
lean::mark_persistent(l_Lean_protectedExt);
return w;
}
