// Lean compiler output
// Module: Init.Lean.Compiler.IR.EmitUtil
// Imports: Init.Control.Conditional Init.Lean.Compiler.InitAttr Init.Lean.Compiler.IR.CompilerM
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
lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_isTailCallTo___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_mkVarJPMaps___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectVar___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkVarJPMaps___closed__1;
uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__2(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
uint8_t l_Lean_Name_isPrefixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectFnBody___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___spec__3(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_formatStx___main___rarg___closed__4;
lean_object* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__1(lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_usesLeanNamespace(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectJP___spec__5(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkVarJPMaps___closed__3;
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___spec__3(lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_UsesLeanNamespace_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_IR_isTailCallTo(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_4) == 11)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_name_eq(x_7, x_1);
return x_11;
}
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
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
lean_object* l_Lean_IR_isTailCallTo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_isTailCallTo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_formatStx___main___rarg___closed__4;
return x_1;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = l_Lean_IR_AltCore_body(x_11);
lean_dec(x_11);
lean_inc(x_5);
x_13 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_12, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_4 = x_18;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_18 = l_Lean_Name_isPrefixOf___main(x_17, x_16);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = l_Lean_NameSet_contains(x_3, x_16);
x_22 = l_Bool_DecidableEq(x_21, x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
lean_inc(x_16);
x_24 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_16, x_23);
lean_inc(x_2);
x_25 = lean_ir_find_env_decl(x_2, x_16);
if (lean_obj_tag(x_25) == 0)
{
x_1 = x_15;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_2);
x_29 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_28, x_2, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_1 = x_15;
x_3 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_27);
x_1 = x_15;
x_3 = x_24;
goto _start;
}
}
}
else
{
lean_dec(x_16);
x_1 = x_15;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_40 = lean_box(x_19);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
case 7:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
lean_dec(x_14);
x_44 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_45 = l_Lean_Name_isPrefixOf___main(x_44, x_43);
x_46 = 1;
x_47 = l_Bool_DecidableEq(x_45, x_46);
if (x_47 == 0)
{
uint8_t x_48; uint8_t x_49; 
x_48 = l_Lean_NameSet_contains(x_3, x_43);
x_49 = l_Bool_DecidableEq(x_48, x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_box(0);
lean_inc(x_43);
x_51 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_43, x_50);
lean_inc(x_2);
x_52 = lean_ir_find_env_decl(x_2, x_43);
if (lean_obj_tag(x_52) == 0)
{
x_1 = x_42;
x_3 = x_51;
goto _start;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_2);
x_56 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_55, x_2, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_1 = x_42;
x_3 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_42);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_56, 0);
lean_dec(x_62);
return x_56;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_54);
x_1 = x_42;
x_3 = x_51;
goto _start;
}
}
}
else
{
lean_dec(x_43);
x_1 = x_42;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_2);
x_67 = lean_box(x_46);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
default: 
{
lean_object* x_69; 
lean_dec(x_14);
x_69 = lean_ctor_get(x_1, 3);
lean_inc(x_69);
lean_dec(x_1);
x_1 = x_69;
goto _start;
}
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_dec(x_1);
lean_inc(x_2);
x_73 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_71, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_1 = x_72;
x_3 = x_76;
goto _start;
}
else
{
uint8_t x_78; 
lean_dec(x_72);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
return x_73;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
case 10:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_1, 3);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_array_get_size(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_82, x_82, x_83, x_84, x_2, x_3);
lean_dec(x_83);
lean_dec(x_82);
return x_85;
}
default: 
{
lean_object* x_86; 
x_86 = lean_box(0);
x_4 = x_86;
goto block_13;
}
}
block_13:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_anyRangeMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_UsesLeanNamespace_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_usesLeanNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_3, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_CollectUsedDecls_collect(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
x_13 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_12, x_3, x_4);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_2 = x_11;
x_4 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_15, x_16);
x_1 = x_14;
x_3 = x_17;
goto _start;
}
case 7:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_20, x_21);
x_1 = x_19;
x_3 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_1 = x_24;
goto _start;
}
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_26, x_2, x_3);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_1 = x_27;
x_3 = x_29;
goto _start;
}
case 10:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_31, x_32, x_2, x_3);
lean_dec(x_31);
return x_33;
}
default: 
{
lean_object* x_34; 
x_34 = lean_box(0);
x_4 = x_34;
goto block_12;
}
}
block_12:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_CollectUsedDecls_collectFnBody(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_init_fn_name_for(x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_IR_CollectUsedDecls_collectInitDecl(x_4, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_5, x_2, x_7);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_inc(x_10);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_IR_CollectUsedDecls_collectInitDecl(x_14, x_2, x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_inc(x_17);
lean_ctor_set(x_15, 0, x_17);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_IR_collectUsedDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_CollectUsedDecls_collectDecl(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectVar___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectVar___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___spec__3(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___spec__3(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___spec__6(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_5, x_1, x_2);
lean_ctor_set(x_3, 0, x_6);
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
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_7, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_13, x_8, x_9);
lean_ctor_set(x_4, 0, x_14);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_16, x_8, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_3 = x_11;
x_4 = x_19;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_1, x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_CollectMaps_collectParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectJP___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_IR_CollectMaps_collectJP___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___spec__3(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___spec__3(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___spec__6(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(x_5, x_1, x_2);
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
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(x_8, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
x_9 = l_Lean_IR_CollectMaps_collectFnBody___main(x_8, x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_IR_CollectMaps_collectFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_IR_CollectMaps_collectFnBody___main(x_12, x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_15, x_10, x_11);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___spec__1(x_17, x_10, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_IR_CollectMaps_collectFnBody___main(x_24, x_2);
x_26 = l_Lean_IR_CollectMaps_collectFnBody___main(x_23, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_22, x_22, x_27, x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(x_30, x_21, x_22);
lean_ctor_set(x_28, 1, x_31);
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
x_34 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___spec__1(x_33, x_21, x_22);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 10:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_36, x_36, x_37, x_2);
lean_dec(x_36);
return x_38;
}
default: 
{
lean_object* x_39; 
x_39 = lean_box(0);
x_3 = x_39;
goto block_9;
}
}
block_9:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_CollectMaps_collectFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_CollectMaps_collectFnBody___main(x_4, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_3, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkVarJPMaps___closed__1;
x_2 = l_Lean_IR_mkVarJPMaps___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_mkVarJPMaps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_mkVarJPMaps___closed__3;
x_3 = l_Lean_IR_CollectMaps_collectDecl(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init_Control_Conditional(lean_object*);
lean_object* initialize_Init_Lean_Compiler_InitAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_EmitUtil(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Conditional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_InitAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix = _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix();
lean_mark_persistent(l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix);
l_Lean_IR_mkVarJPMaps___closed__1 = _init_l_Lean_IR_mkVarJPMaps___closed__1();
lean_mark_persistent(l_Lean_IR_mkVarJPMaps___closed__1);
l_Lean_IR_mkVarJPMaps___closed__2 = _init_l_Lean_IR_mkVarJPMaps___closed__2();
lean_mark_persistent(l_Lean_IR_mkVarJPMaps___closed__2);
l_Lean_IR_mkVarJPMaps___closed__3 = _init_l_Lean_IR_mkVarJPMaps___closed__3();
lean_mark_persistent(l_Lean_IR_mkVarJPMaps___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
