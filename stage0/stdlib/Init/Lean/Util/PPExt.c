// Lean compiler output
// Module: Init.Lean.Util.PPExt
// Imports: Init.Lean.Environment Init.Lean.MetavarContext
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
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_PPExprFnRef;
extern lean_object* l_Lean_verboseOption___closed__3;
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_ppExprExt___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPPExprFnExtension(lean_object*);
lean_object* l_Lean_mkPPExprFnExtension___closed__1;
lean_object* l_Lean_mkPPExprFnRef___closed__1;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppExprExt___closed__3;
lean_object* l_Lean_ppExprExt___elambda__2(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___closed__2;
lean_object* l_Lean_ppOldOption___closed__2;
lean_object* l_Lean_mkPPExprFnRef(lean_object*);
lean_object* l_Lean_ppOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ppOldOption___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_ppExpr___closed__2;
lean_object* l_Lean_ppOldOption(lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1;
lean_object* l_Lean_ppExprExt;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExpr___closed__1;
lean_object* l_Lean_ppOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_pp_expr(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_mkPPExprFnRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppOld___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_mkPPExprFnRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkPPExprFnRef___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_3);
x_10 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_11 = lean_io_ref_get(x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
lean_dec(x_12);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_io_ref_get(x_10, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_ref_reset(x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_inc(x_16);
x_23 = x_16;
x_24 = lean_array_push(x_18, x_23);
x_25 = lean_io_ref_set(x_10, x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_16);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_49 = l_coeDecidableEq(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_53 = lean_io_ref_get(x_52, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_get_size(x_54);
lean_dec(x_54);
x_57 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1;
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_io_ref_get(x_52, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_io_ref_reset(x_52, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_inc(x_58);
x_65 = x_58;
x_66 = lean_array_push(x_60, x_65);
x_67 = lean_io_ref_set(x_52, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_58);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_60);
lean_dec(x_58);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_77 = x_62;
} else {
 lean_dec_ref(x_62);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_53, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_85 = x_53;
} else {
 lean_dec_ref(x_53);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_3);
if (x_87 == 0)
{
return x_3;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_3);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* _init_l_Lean_mkPPExprFnExtension___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPExprFnRef;
x_2 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_mkPPExprFnExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkPPExprFnExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ppExprExt___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
lean_object* l_Lean_ppExprExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppExprExt___elambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppExprExt___elambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_ppExprExt___closed__1;
x_3 = l_Lean_ppExprExt___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_ppExprExt___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppExprExt___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_ppExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppOld");
return x_1;
}
}
lean_object* _init_l_Lean_ppExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ppExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
lean_inc(x_2);
x_6 = l_Lean_MetavarContext_instantiateMVars(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_ppExpr___closed__2;
x_9 = 1;
x_10 = l_Lean_KVMap_getBool(x_4, x_8, x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_expr_dbg_to_string(x_7);
lean_dec(x_7);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_ppExprExt;
x_15 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_14, x_1);
x_16 = lean_apply_5(x_15, x_1, x_2, x_3, x_4, x_7);
return x_16;
}
}
}
lean_object* _init_l_Lean_ppOldOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable/enable old pretty printer");
return x_1;
}
}
lean_object* _init_l_Lean_ppOldOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_verboseOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_ppOldOption___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_ppOldOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_ppExpr___closed__2;
x_3 = l_Lean_ppOldOption___closed__2;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_PPExt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkPPExprFnRef___closed__1 = _init_l_Lean_mkPPExprFnRef___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnRef___closed__1);
res = l_Lean_mkPPExprFnRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PPExprFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PPExprFnRef);
lean_dec_ref(res);
l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1);
l_Lean_mkPPExprFnExtension___closed__1 = _init_l_Lean_mkPPExprFnExtension___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnExtension___closed__1);
l_Lean_ppExprExt___closed__1 = _init_l_Lean_ppExprExt___closed__1();
lean_mark_persistent(l_Lean_ppExprExt___closed__1);
l_Lean_ppExprExt___closed__2 = _init_l_Lean_ppExprExt___closed__2();
lean_mark_persistent(l_Lean_ppExprExt___closed__2);
l_Lean_ppExprExt___closed__3 = _init_l_Lean_ppExprExt___closed__3();
lean_mark_persistent(l_Lean_ppExprExt___closed__3);
res = l_Lean_mkPPExprFnExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExprExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExprExt);
lean_dec_ref(res);
l_Lean_ppExpr___closed__1 = _init_l_Lean_ppExpr___closed__1();
lean_mark_persistent(l_Lean_ppExpr___closed__1);
l_Lean_ppExpr___closed__2 = _init_l_Lean_ppExpr___closed__2();
lean_mark_persistent(l_Lean_ppExpr___closed__2);
l_Lean_ppOldOption___closed__1 = _init_l_Lean_ppOldOption___closed__1();
lean_mark_persistent(l_Lean_ppOldOption___closed__1);
l_Lean_ppOldOption___closed__2 = _init_l_Lean_ppOldOption___closed__2();
lean_mark_persistent(l_Lean_ppOldOption___closed__2);
res = l_Lean_ppOldOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
