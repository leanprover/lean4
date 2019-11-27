// Lean compiler output
// Module: Init.Lean.Modifiers
// Imports: Init.Lean.Environment
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
uint8_t lean_is_protected(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___closed__1;
lean_object* l_Lean_privateExt___elambda__1(lean_object*);
lean_object* l_Lean_protectedExt___closed__3;
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux(lean_object*);
uint8_t l_Lean_isPrivateName___main(lean_object*);
lean_object* l_Lean_protectedExt___closed__5;
lean_object* l_Lean_privateHeader;
extern lean_object* l_Array_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPrivateExtension___spec__1(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
uint8_t lean_is_private_name(lean_object*);
lean_object* l_Lean_isPrivateName___boxed(lean_object*);
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___main___boxed(lean_object*);
lean_object* l_Lean_privateExt___closed__2;
lean_object* l_Lean_isPrivateName___main___boxed(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_private_prefix(lean_object*);
lean_object* l_Lean_EnvExtension_setStateUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_privateExt___closed__1;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* lean_add_protected(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt;
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__2(lean_object*);
lean_object* lean_private_prefix(lean_object*);
lean_object* l_Lean_isPrivateNameExport___boxed(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_mkPrivateExtension(lean_object*);
lean_object* lean_mk_private_name(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___main(lean_object*);
lean_object* l___private_Init_Lean_Modifiers_1__privateToUserNameAux___main(lean_object*);
lean_object* l_Lean_mkProtectedExtension(lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_protectedExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateExtension___closed__1;
lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object*);
lean_object* l_Lean_privateExt;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_namespacesExt___closed__1;
lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*);
lean_object* l_Lean_isProtected___boxed(lean_object*, lean_object*);
lean_object* l_Lean_protectedExt___elambda__1(lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Modifiers_1__privateToUserNameAux(lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_privateHeader___closed__2;
lean_object* l_Lean_protectedExt___elambda__4(lean_object*);
lean_object* l_Lean_protectedExt___closed__4;
lean_object* l_Lean_mkProtectedExtension___closed__2;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_privateHeader___closed__1;
lean_object* l_Lean_protectedExt___closed__2;
lean_object* l_Lean_mkProtectedExtension___closed__1;
lean_object* _init_l_Lean_mkProtectedExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected");
return x_1;
}
}
lean_object* _init_l_Lean_mkProtectedExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkProtectedExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkProtectedExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkProtectedExtension___closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_protectedExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_protectedExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_protectedExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_protectedExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_protectedExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_protectedExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_protectedExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_namespacesExt___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_protectedExt___closed__1;
x_4 = l_Lean_protectedExt___closed__2;
x_5 = l_Lean_protectedExt___closed__3;
x_6 = l_Lean_protectedExt___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_protectedExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_protectedExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_protectedExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_protectedExt___elambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_protectedExt___elambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_add_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_protected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_protectedExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isProtected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_protected(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPrivateExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = 1;
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Bool_DecidableEq(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_3);
x_11 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_12 = lean_io_ref_get(x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_io_ref_get(x_11, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_ref_reset(x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_17);
x_24 = x_17;
x_25 = lean_array_push(x_19, x_24);
x_26 = lean_io_ref_set(x_11, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_17);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_17);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_49 = 1;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
x_51 = l_Bool_DecidableEq(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_55 = lean_io_ref_get(x_54, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_get_size(x_56);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_1);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_io_ref_get(x_54, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_io_ref_reset(x_54, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_60);
x_67 = x_60;
x_68 = lean_array_push(x_62, x_67);
x_69 = lean_io_ref_set(x_54, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_60);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_60);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_85 = lean_ctor_get(x_55, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_87 = x_55;
} else {
 lean_dec_ref(x_55);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
return x_3;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_3, 0);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_3);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* _init_l_Lean_mkPrivateExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_mkPrivateExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkPrivateExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPrivateExtension___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_privateExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_privateExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_privateExt___elambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_privateExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_privateExt___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_privateHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private");
return x_1;
}
}
lean_object* _init_l_Lean_privateHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_privateHeader___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_privateHeader() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_privateHeader___closed__2;
return x_1;
}
}
lean_object* lean_mk_private_prefix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_privateExt;
x_3 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_2, x_1);
lean_inc(x_1);
x_4 = lean_environment_main_module(x_1);
x_5 = l_Lean_privateHeader;
x_6 = l_Lean_Name_append___main(x_5, x_4);
lean_inc(x_3);
x_7 = lean_name_mk_numeral(x_6, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_10 = l_Lean_EnvExtension_setStateUnsafe___rarg(x_2, x_1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
lean_object* lean_mk_private_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_mk_private_prefix(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Name_append___main(x_5, x_2);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_Name_append___main(x_8, x_2);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
uint8_t l_Lean_isPrivateName___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_privateHeader;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
default: 
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_1 = x_8;
goto _start;
}
}
}
}
lean_object* l_Lean_isPrivateName___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivateName___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_isPrivateName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName___main(x_1);
return x_2;
}
}
lean_object* l_Lean_isPrivateName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isPrivateName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_is_private_name(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isPrivateName___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_isPrivateNameExport___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_private_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Modifiers_1__privateToUserNameAux___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Lean_Modifiers_1__privateToUserNameAux___main(x_2);
x_5 = lean_name_mk_string(x_4, x_3);
return x_5;
}
default: 
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
}
}
}
lean_object* l___private_Init_Lean_Modifiers_1__privateToUserNameAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Modifiers_1__privateToUserNameAux___main(x_1);
return x_2;
}
}
lean_object* lean_private_to_user_name(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_isPrivateName___main(x_1);
x_3 = 1;
x_4 = l_Bool_DecidableEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Init_Lean_Modifiers_1__privateToUserNameAux___main(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Modifiers_2__privatePrefixAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Modifiers_2__privatePrefixAux___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Modifiers_2__privatePrefixAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Modifiers_2__privatePrefixAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_private_prefix(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_isPrivateName___main(x_1);
x_3 = 1;
x_4 = l_Bool_DecidableEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Init_Lean_Modifiers_2__privatePrefixAux___main(x_1);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Modifiers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkProtectedExtension___closed__1 = _init_l_Lean_mkProtectedExtension___closed__1();
lean_mark_persistent(l_Lean_mkProtectedExtension___closed__1);
l_Lean_mkProtectedExtension___closed__2 = _init_l_Lean_mkProtectedExtension___closed__2();
lean_mark_persistent(l_Lean_mkProtectedExtension___closed__2);
l_Lean_protectedExt___closed__1 = _init_l_Lean_protectedExt___closed__1();
lean_mark_persistent(l_Lean_protectedExt___closed__1);
l_Lean_protectedExt___closed__2 = _init_l_Lean_protectedExt___closed__2();
lean_mark_persistent(l_Lean_protectedExt___closed__2);
l_Lean_protectedExt___closed__3 = _init_l_Lean_protectedExt___closed__3();
lean_mark_persistent(l_Lean_protectedExt___closed__3);
l_Lean_protectedExt___closed__4 = _init_l_Lean_protectedExt___closed__4();
lean_mark_persistent(l_Lean_protectedExt___closed__4);
l_Lean_protectedExt___closed__5 = _init_l_Lean_protectedExt___closed__5();
lean_mark_persistent(l_Lean_protectedExt___closed__5);
res = l_Lean_mkProtectedExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
l_Lean_mkPrivateExtension___closed__1 = _init_l_Lean_mkPrivateExtension___closed__1();
lean_mark_persistent(l_Lean_mkPrivateExtension___closed__1);
l_Lean_privateExt___closed__1 = _init_l_Lean_privateExt___closed__1();
lean_mark_persistent(l_Lean_privateExt___closed__1);
l_Lean_privateExt___closed__2 = _init_l_Lean_privateExt___closed__2();
lean_mark_persistent(l_Lean_privateExt___closed__2);
res = l_Lean_mkPrivateExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_privateExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_privateExt);
lean_dec_ref(res);
l_Lean_privateHeader___closed__1 = _init_l_Lean_privateHeader___closed__1();
lean_mark_persistent(l_Lean_privateHeader___closed__1);
l_Lean_privateHeader___closed__2 = _init_l_Lean_privateHeader___closed__2();
lean_mark_persistent(l_Lean_privateHeader___closed__2);
l_Lean_privateHeader = _init_l_Lean_privateHeader();
lean_mark_persistent(l_Lean_privateHeader);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
