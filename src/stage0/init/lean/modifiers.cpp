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
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_mkProtectedExtension___lambda__2(obj*);
namespace lean {
obj* add_protected_core(obj*, obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1(uint8, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_Inhabited;
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_isProtected___boxed(obj*, obj*);
obj* l_Lean_protectedExt___elambda__1(obj*);
extern obj* l___private_init_lean_environment_9__persistentEnvExtensionsRef;
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
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_protectedExt;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(obj*, obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_protectedExt___elambda__2___rarg(obj*, obj*);
obj* l_Lean_protectedExt___elambda__2(uint8);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
namespace lean {
uint8 is_protected_core(obj*, obj*);
}
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
obj* l_Lean_protectedExt___elambda__2___boxed(obj*);
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_lt(x_4, x_0);
if (x_5 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_4);
x_7 = lean::array_swap(x_2, x_3, x_0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = l_Lean_Inhabited;
x_10 = lean::array_get(x_9, x_2, x_4);
x_11 = l_Lean_Name_quickLt(x_10, x_1);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_4, x_13);
lean::dec(x_4);
x_4 = x_14;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_17 = lean::array_swap(x_2, x_3, x_4);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_3, x_18);
lean::dec(x_3);
x_21 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_2 = x_17;
x_3 = x_19;
x_4 = x_21;
goto _start;
}
}
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_5 = lean::nat_add(x_1, x_2);
x_6 = lean::mk_nat_obj(2ul);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
x_11 = l_Lean_Inhabited;
x_12 = lean::array_get(x_11, x_0, x_7);
x_13 = lean::array_get(x_11, x_0, x_1);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
lean::dec(x_13);
lean::dec(x_12);
if (x_14 == 0)
{
x_9 = x_0;
goto lbl_10;
}
else
{
obj* x_17; 
x_17 = lean::array_swap(x_0, x_1, x_7);
x_9 = x_17;
goto lbl_10;
}
lbl_10:
{
obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_18 = l_Lean_Inhabited;
x_19 = lean::array_get(x_18, x_9, x_2);
x_20 = lean::array_get(x_18, x_9, x_1);
x_21 = l_Lean_Name_quickLt(x_19, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::array_get(x_18, x_9, x_7);
x_24 = l_Lean_Name_quickLt(x_23, x_19);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_1);
x_29 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_2, x_19, x_9, x_1, x_1);
lean::dec(x_19);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_36 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_33, x_1, x_31);
x_37 = lean::mk_nat_obj(1ul);
x_38 = lean::nat_add(x_31, x_37);
lean::dec(x_31);
x_0 = x_36;
x_1 = x_38;
goto _start;
}
else
{
obj* x_42; obj* x_44; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_19);
x_42 = lean::array_swap(x_9, x_7, x_2);
lean::dec(x_7);
x_44 = lean::array_get(x_18, x_42, x_2);
lean::inc(x_1);
lean::inc(x_1);
x_47 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_2, x_44, x_42, x_1, x_1);
lean::dec(x_44);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_51, x_1, x_49);
x_55 = lean::mk_nat_obj(1ul);
x_56 = lean::nat_add(x_49, x_55);
lean::dec(x_49);
x_0 = x_54;
x_1 = x_56;
goto _start;
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; uint8 x_63; 
lean::dec(x_19);
x_60 = lean::array_swap(x_9, x_1, x_2);
x_61 = lean::array_get(x_18, x_60, x_7);
x_62 = lean::array_get(x_18, x_60, x_2);
x_63 = l_Lean_Name_quickLt(x_61, x_62);
lean::dec(x_61);
if (x_63 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_1);
x_68 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_2, x_62, x_60, x_1, x_1);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_68, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_68, 1);
lean::inc(x_72);
lean::dec(x_68);
x_75 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_72, x_1, x_70);
x_76 = lean::mk_nat_obj(1ul);
x_77 = lean::nat_add(x_70, x_76);
lean::dec(x_70);
x_0 = x_75;
x_1 = x_77;
goto _start;
}
else
{
obj* x_81; obj* x_83; obj* x_86; obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_62);
x_81 = lean::array_swap(x_60, x_7, x_2);
lean::dec(x_7);
x_83 = lean::array_get(x_18, x_81, x_2);
lean::inc(x_1);
lean::inc(x_1);
x_86 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_2, x_83, x_81, x_1, x_1);
lean::dec(x_83);
x_88 = lean::cnstr_get(x_86, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_86, 1);
lean::inc(x_90);
lean::dec(x_86);
x_93 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_90, x_1, x_88);
x_94 = lean::mk_nat_obj(1ul);
x_95 = lean::nat_add(x_88, x_94);
lean::dec(x_88);
x_0 = x_93;
x_1 = x_95;
goto _start;
}
}
}
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_12; uint8 x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_0, 0);
x_13 = lean_name_dec_eq(x_9, x_12);
lean::dec(x_9);
if (x_13 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_2, x_15);
lean::dec(x_2);
x_2 = x_16;
goto _start;
}
else
{
lean::dec(x_2);
return x_13;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 4);
lean::inc(x_10);
x_12 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
lean::inc(x_4);
x_14 = lean::thunk_pure(x_4);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_4);
x_17 = l_Array_empty___closed__1;
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_16);
x_19 = l___private_init_lean_environment_9__persistentEnvExtensionsRef;
x_20 = lean::io_ref_get(x_19, x_1);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; 
x_21 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_set(x_20, 0, lean::box(0));
 lean::cnstr_set(x_20, 1, lean::box(0));
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = lean::mk_nat_obj(0ul);
x_27 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(x_0, x_21, x_26);
lean::dec(x_21);
lean::dec(x_0);
if (x_27 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::box(0);
if (lean::is_scalar(x_25)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_25;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = l_Lean_registerEnvExtensionUnsafe___rarg(x_18, x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_32, 0);
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_32);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_30);
lean::cnstr_set(x_38, 1, x_35);
x_39 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_39, 0, x_33);
lean::cnstr_set(x_39, 1, x_2);
lean::cnstr_set(x_39, 2, x_6);
lean::cnstr_set(x_39, 3, x_8);
lean::cnstr_set(x_39, 4, x_10);
lean::cnstr_set_scalar(x_39, sizeof(void*)*5, x_12);
x_40 = x_39;
x_41 = lean::io_ref_get(x_19, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
x_42 = lean::cnstr_get(x_41, 0);
x_44 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_46 = x_41;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_41);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_30);
lean::cnstr_set(x_47, 1, x_44);
x_48 = lean::io_ref_reset(x_19, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_49 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_51 = x_48;
} else {
 lean::inc(x_49);
 lean::dec(x_48);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_49);
x_53 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean::inc(x_40);
x_55 = x_40;
x_56 = lean::array_push(x_42, x_55);
x_57 = lean::io_ref_set(x_19, x_56, x_52);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_60 = x_57;
} else {
 lean::inc(x_58);
 lean::dec(x_57);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_40);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_40);
x_63 = lean::cnstr_get(x_57, 0);
x_65 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 x_67 = x_57;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_57);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
}
}
else
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_40);
lean::dec(x_42);
x_71 = lean::cnstr_get(x_48, 0);
x_73 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 x_75 = x_48;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_48);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_71);
lean::cnstr_set(x_76, 1, x_73);
return x_76;
}
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_40);
x_78 = lean::cnstr_get(x_41, 0);
x_80 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_82 = x_41;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_41);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_78);
lean::cnstr_set(x_83, 1, x_80);
return x_83;
}
}
else
{
obj* x_88; obj* x_90; obj* x_92; obj* x_93; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_2);
x_88 = lean::cnstr_get(x_32, 0);
x_90 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_92 = x_32;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_32);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_88);
lean::cnstr_set(x_93, 1, x_90);
return x_93;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_18);
x_98 = l_Lean_Name_toString___closed__1;
x_99 = l_Lean_Name_toStringWithSep___main(x_98, x_2);
x_100 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_101 = lean::string_append(x_100, x_99);
lean::dec(x_99);
x_103 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_104 = lean::string_append(x_101, x_103);
if (lean::is_scalar(x_25)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_25;
 lean::cnstr_set_tag(x_25, 1);
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_23);
return x_105;
}
}
else
{
obj* x_112; obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_112 = lean::cnstr_get(x_20, 0);
x_114 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_116 = x_20;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_20);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_112);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
}
obj* l_Lean_mkProtectedExtension___lambda__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (x_0 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Lean_mkProtectedExtension___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
x_5 = lean::array_get_size(x_4);
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_4, x_9, x_7);
lean::dec(x_7);
return x_10;
}
}
obj* _init_l_Lean_mkProtectedExtension___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("protected");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProtectedExtension___lambda__1___boxed), 3, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkProtectedExtension___lambda__2), 1, 0);
x_6 = 0;
x_7 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_4);
lean::cnstr_set(x_7, 4, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*5, x_6);
x_8 = x_7;
return x_8;
}
}
obj* l_Lean_mkProtectedExtension(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_mkProtectedExtension___closed__1;
x_2 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__3(x_1, x_0);
return x_2;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_qsort_1__partitionAux___main___at_Lean_mkProtectedExtension___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_qsortAux___main___at_Lean_mkProtectedExtension___spec__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__4(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_Lean_mkProtectedExtension___lambda__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_protectedExt___elambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
return x_4;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_protectedExt___elambda__2(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_protectedExt___elambda__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_protectedExt___elambda__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_protectedExt___elambda__2___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_protectedExt___elambda__2(x_1);
return x_2;
}
}
namespace lean {
obj* add_protected_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_protectedExt;
x_3 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_2, x_0, x_1);
return x_3;
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; 
x_8 = lean::nat_add(x_2, x_3);
x_9 = lean::mk_nat_obj(2ul);
x_10 = lean::nat_div(x_8, x_9);
lean::dec(x_8);
x_12 = l_Lean_Inhabited;
x_13 = lean::array_get(x_12, x_0, x_10);
x_14 = l_Lean_Name_quickLt(x_13, x_1);
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_3);
x_16 = l_Lean_Name_quickLt(x_1, x_13);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_2);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_13);
return x_19;
}
else
{
obj* x_21; uint8 x_22; 
lean::dec(x_13);
x_21 = lean::mk_nat_obj(0ul);
x_22 = lean::nat_dec_eq(x_10, x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_sub(x_10, x_23);
lean::dec(x_10);
x_3 = x_24;
goto _start;
}
else
{
obj* x_29; 
lean::dec(x_10);
lean::dec(x_2);
x_29 = lean::box(0);
return x_29;
}
}
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_13);
lean::dec(x_2);
x_32 = lean::mk_nat_obj(1ul);
x_33 = lean::nat_add(x_10, x_32);
lean::dec(x_10);
x_2 = x_33;
goto _start;
}
}
}
}
namespace lean {
uint8 is_protected_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Environment_getModuleIdxFor(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_6; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_0);
lean::dec(x_0);
x_6 = l_Lean_NameSet_contains(x_4, x_1);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = l_Lean_protectedExt;
x_12 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_11, x_0, x_8);
lean::dec(x_8);
lean::dec(x_0);
x_15 = lean::array_get_size(x_12);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_19 = lean::mk_nat_obj(0ul);
x_20 = l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(x_12, x_1, x_19, x_17);
lean::dec(x_1);
lean::dec(x_12);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_23; 
x_23 = 0;
return x_23;
}
else
{
uint8 x_25; 
lean::dec(x_20);
x_25 = 1;
return x_25;
}
}
}
}
}
obj* l_Array_binSearchAux___main___at_Lean_isProtected___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_binSearchAux___main___at_Lean_isProtected___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_isProtected___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::is_protected_core(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
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
