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
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2(obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
namespace lean {
obj* add_protected_core(obj*, obj*);
}
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Lean_mkProtectedExtension___lambda__1(uint8, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Lean_isProtected___boxed(obj*, obj*);
obj* l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2(obj*);
obj* l_Lean_protectedExt___elambda__1(obj*);
extern obj* l___private_init_lean_environment_9__persistentEnvExtensionsRef;
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___rarg(obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__1(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_mkProtectedExtension___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_protectedExt;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_mkProtectedExtension___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_protectedExt___elambda__2___rarg(obj*, obj*);
obj* l_Lean_protectedExt___elambda__2(uint8);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
namespace lean {
uint8 is_protected_core(obj*, obj*);
}
obj* l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2___boxed(obj*, obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_mkProtectedExtension(obj*);
obj* l_Lean_protectedExt___elambda__2___boxed(obj*);
obj* l_Lean_protectedExt___elambda__2___rarg___boxed(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__1(obj* x_0, obj* x_1) {
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
x_27 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2(x_0, x_21, x_26);
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
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_PersistentEnvExtension_inhabited___rarg___lambda__2), 1, 0);
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
x_2 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkProtectedExtension___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_mkProtectedExtension___spec__2(x_0, x_1, x_2);
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
namespace lean {
uint8 is_protected_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_5; 
x_2 = l_Lean_protectedExt;
x_3 = l_Lean_PersistentEnvExtension_getState___rarg(x_2, x_0);
lean::dec(x_0);
x_5 = l_Lean_NameSet_contains(x_3, x_1);
lean::dec(x_1);
return x_5;
}
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
