// Lean compiler output
// Module: init.lean.compiler.ir.emitutil
// Imports: init.control.conditional init.lean.compiler.ir.compilerm
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
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectFnBody___main(obj*, obj*);
obj* l_Lean_IR_mkVarJPMaps___closed__1;
obj* l_Lean_IR_CollectUsedDecls_collect(obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(obj*, uint8, obj*);
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectVar___main___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(obj*, obj*, uint8);
obj* l_Lean_IR_CollectMaps_collectDecl(obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___main(obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(obj*, obj*, obj*);
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__2(obj*);
obj* l_Lean_IR_mkVarJPMaps(obj*);
obj* l_Lean_IR_CollectMaps_collectVar___boxed(obj*, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_CollectMaps_collectJP(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectJP___main(obj*, obj*, obj*);
obj* l_Lean_IR_CollectUsedDecls_collectFnBody___main(obj*, obj*);
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__1(obj*);
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(obj*, obj*, obj*);
obj* l_Lean_IR_collectUsedDecls(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectVar(obj*, uint8, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___main___spec__4(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectDecl___main(obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace___boxed(obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectJP___main___spec__5(obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectVar___main(obj*, uint8, obj*);
obj* l_Lean_IR_CollectMaps_collectFnBody(obj*, obj*);
obj* l_Lean_IR_usesLeanNamespace(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___main___spec__4(obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_IR_CollectUsedDecls_collectFnBody(obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectParams___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Lean_Name_isPrefixOf___main(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2___boxed(obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2___boxed(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_IR_usesLeanNamespace___main___boxed(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectParams(obj*, obj*);
obj* _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_17; 
x_11 = lean::array_fget(x_0, x_1);
x_12 = l_Lean_IR_AltCore_body___main(x_11);
lean::dec(x_11);
x_14 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_12, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_14, 1);
lean::inc(x_18);
lean::dec(x_14);
x_21 = lean::mk_nat_obj(1ul);
x_22 = lean::nat_add(x_1, x_21);
lean::dec(x_1);
x_1 = x_22;
x_3 = x_18;
goto _start;
}
else
{
obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_28 = x_14;
} else {
 lean::inc(x_26);
 lean::dec(x_14);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
switch (lean::obj_tag(x_5)) {
case 6:
{
obj* x_7; obj* x_10; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_14 = l_Lean_Name_isPrefixOf___main(x_13, x_10);
if (x_14 == 0)
{
uint8 x_16; 
lean::inc(x_2);
x_16 = l_Lean_NameSet_contains(x_2, x_10);
if (x_16 == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::box(0);
lean::inc(x_10);
x_19 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_10, x_17);
x_20 = l_Lean_IR_findEnvDecl(x_1, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_20) == 0)
{
x_0 = x_7;
x_2 = x_19;
goto _start;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_29; obj* x_30; uint8 x_32; 
x_26 = lean::cnstr_get(x_23, 2);
lean::inc(x_26);
lean::dec(x_23);
x_29 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_26, x_1, x_19);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::unbox(x_30);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_0 = x_7;
x_2 = x_33;
goto _start;
}
else
{
obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_7);
x_38 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_40 = x_29;
} else {
 lean::inc(x_38);
 lean::dec(x_29);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean::dec(x_23);
x_0 = x_7;
x_2 = x_19;
goto _start;
}
}
}
else
{
lean::dec(x_10);
x_0 = x_7;
goto _start;
}
}
else
{
uint8 x_48; obj* x_49; obj* x_50; 
lean::dec(x_7);
lean::dec(x_10);
x_48 = 1;
x_49 = lean::box(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_2);
return x_50;
}
}
case 7:
{
obj* x_51; obj* x_54; obj* x_57; uint8 x_58; 
x_51 = lean::cnstr_get(x_0, 2);
lean::inc(x_51);
lean::dec(x_0);
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
lean::dec(x_5);
x_57 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_58 = l_Lean_Name_isPrefixOf___main(x_57, x_54);
if (x_58 == 0)
{
uint8 x_60; 
lean::inc(x_2);
x_60 = l_Lean_NameSet_contains(x_2, x_54);
if (x_60 == 0)
{
obj* x_61; obj* x_63; obj* x_64; 
x_61 = lean::box(0);
lean::inc(x_54);
x_63 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_54, x_61);
x_64 = l_Lean_IR_findEnvDecl(x_1, x_54);
lean::dec(x_54);
if (lean::obj_tag(x_64) == 0)
{
x_0 = x_51;
x_2 = x_63;
goto _start;
}
else
{
obj* x_67; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; obj* x_73; obj* x_74; uint8 x_76; 
x_70 = lean::cnstr_get(x_67, 2);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_70, x_1, x_63);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::unbox(x_74);
if (x_76 == 0)
{
obj* x_77; 
x_77 = lean::cnstr_get(x_73, 1);
lean::inc(x_77);
lean::dec(x_73);
x_0 = x_51;
x_2 = x_77;
goto _start;
}
else
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_51);
x_82 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_84 = x_73;
} else {
 lean::inc(x_82);
 lean::dec(x_73);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_74);
lean::cnstr_set(x_85, 1, x_82);
return x_85;
}
}
else
{
lean::dec(x_67);
x_0 = x_51;
x_2 = x_63;
goto _start;
}
}
}
else
{
lean::dec(x_54);
x_0 = x_51;
goto _start;
}
}
else
{
uint8 x_92; obj* x_93; obj* x_94; 
lean::dec(x_51);
lean::dec(x_54);
x_92 = 1;
x_93 = lean::box(x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_2);
return x_94;
}
}
default:
{
obj* x_96; 
lean::dec(x_5);
x_96 = lean::cnstr_get(x_0, 2);
lean::inc(x_96);
lean::dec(x_0);
x_0 = x_96;
goto _start;
}
}
}
case 1:
{
obj* x_100; obj* x_102; obj* x_105; obj* x_106; uint8 x_108; 
x_100 = lean::cnstr_get(x_0, 2);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_0, 3);
lean::inc(x_102);
lean::dec(x_0);
x_105 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_100, x_1, x_2);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::unbox(x_106);
if (x_108 == 0)
{
obj* x_109; 
x_109 = lean::cnstr_get(x_105, 1);
lean::inc(x_109);
lean::dec(x_105);
x_0 = x_102;
x_2 = x_109;
goto _start;
}
else
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_102);
x_114 = lean::cnstr_get(x_105, 1);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 x_116 = x_105;
} else {
 lean::inc(x_114);
 lean::dec(x_105);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_106);
lean::cnstr_set(x_117, 1, x_114);
return x_117;
}
}
case 10:
{
obj* x_118; obj* x_121; obj* x_122; 
x_118 = lean::cnstr_get(x_0, 2);
lean::inc(x_118);
lean::dec(x_0);
x_121 = lean::mk_nat_obj(0ul);
x_122 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_118, x_121, x_1, x_2);
lean::dec(x_118);
return x_122;
}
default:
{
obj* x_124; 
x_124 = lean::box(0);
x_3 = x_124;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_126; 
lean::dec(x_3);
x_126 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_126 == 0)
{
obj* x_127; 
x_127 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_127;
goto _start;
}
else
{
uint8 x_131; obj* x_132; obj* x_133; 
lean::dec(x_0);
x_131 = 0;
x_132 = lean::box(x_131);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_2);
return x_133;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UsesLeanNamespace_visitFnBody(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_usesLeanNamespace___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_2, x_0, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
else
{
uint8 x_11; obj* x_12; 
lean::dec(x_1);
x_11 = 0;
x_12 = lean::box(x_11);
return x_12;
}
}
}
obj* l_Lean_IR_usesLeanNamespace___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_usesLeanNamespace(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_usesLeanNamespace___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_usesLeanNamespace(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_CollectUsedDecls_collect(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_0, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; 
x_9 = lean::array_fget(x_0, x_1);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_13 = l_Lean_IR_AltCore_body___main(x_9);
lean::dec(x_9);
x_15 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_13, x_2);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_1 = x_11;
x_2 = x_16;
goto _start;
}
}
}
obj* l_Lean_IR_CollectUsedDecls_collectFnBody___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
switch (lean::obj_tag(x_4)) {
case 6:
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::box(0);
x_13 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_9, x_12);
x_0 = x_6;
x_1 = x_13;
goto _start;
}
case 7:
{
obj* x_15; obj* x_18; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_0, 2);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
lean::dec(x_4);
x_21 = lean::box(0);
x_22 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_18, x_21);
x_0 = x_15;
x_1 = x_22;
goto _start;
}
default:
{
obj* x_25; 
lean::dec(x_4);
x_25 = lean::cnstr_get(x_0, 2);
lean::inc(x_25);
lean::dec(x_0);
x_0 = x_25;
goto _start;
}
}
}
case 1:
{
obj* x_29; obj* x_31; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_0, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 3);
lean::inc(x_31);
lean::dec(x_0);
x_34 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_29, x_1);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_0 = x_31;
x_1 = x_35;
goto _start;
}
case 10:
{
obj* x_39; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_0, 2);
lean::inc(x_39);
lean::dec(x_0);
x_42 = lean::mk_nat_obj(0ul);
x_43 = l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_39, x_42, x_1);
lean::dec(x_39);
return x_43;
}
default:
{
obj* x_45; 
x_45 = lean::box(0);
x_2 = x_45;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_47; 
lean::dec(x_2);
x_47 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_47 == 0)
{
obj* x_48; 
x_48 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_48;
goto _start;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_0);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_1);
return x_53;
}
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_CollectUsedDecls_collectFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_collectUsedDecls(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_2, x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::nat_dec_eq(x_3, x_0);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::array_get_size(x_0);
x_10 = lean::usize_of_nat(x_2);
x_11 = lean::usize_modn(x_10, x_9);
lean::dec(x_9);
x_13 = lean::array_uget(x_0, x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::array_uset(x_0, x_11, x_14);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_1, x_0, x_9);
x_11 = l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(x_2, x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_mul(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_4, x_6);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___main___spec__4(x_8, x_1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_11; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_8 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_10 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::nat_dec_eq(x_4, x_0);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_13 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_13 = x_10;
}
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_6);
lean::cnstr_set(x_13, 2, x_12);
return x_13;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_4);
x_16 = lean::box(x_1);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_8);
return x_17;
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::array_get_size(x_5);
x_9 = lean::usize_of_nat(x_1);
x_10 = lean::usize_modn(x_9, x_8);
x_11 = lean::array_uget(x_5, x_10);
x_12 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_16 = lean::box(x_2);
x_17 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_11);
x_18 = lean::array_uset(x_5, x_10, x_17);
x_19 = lean::nat_dec_le(x_14, x_8);
lean::dec(x_8);
if (x_19 == 0)
{
obj* x_22; 
lean::dec(x_7);
x_22 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(x_14, x_18);
return x_22;
}
else
{
obj* x_23; 
if (lean::is_scalar(x_7)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_7;
}
lean::cnstr_set(x_23, 0, x_14);
lean::cnstr_set(x_23, 1, x_18);
return x_23;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_8);
x_25 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_1, x_2, x_11);
x_26 = lean::array_uset(x_5, x_10, x_25);
if (lean::is_scalar(x_7)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_7;
}
lean::cnstr_set(x_27, 0, x_3);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_Lean_IR_CollectMaps_collectVar___main(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_3, x_0, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_0, x_3, x_2);
return x_4;
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_IR_CollectMaps_collectVar___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_CollectMaps_collectVar___main(x_0, x_3, x_2);
return x_4;
}
}
obj* l_Lean_IR_CollectMaps_collectVar(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_3, x_0, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* l_Lean_IR_CollectMaps_collectVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_CollectMaps_collectVar(x_0, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; uint8 x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1 + 1);
lean::dec(x_8);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_3, 0);
x_18 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_20 = x_3;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_3);
 x_20 = lean::box(0);
}
x_21 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_16, x_9, x_11);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_18);
x_2 = x_14;
x_3 = x_22;
goto _start;
}
}
}
obj* l_Lean_IR_CollectMaps_collectParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_0, x_0, x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_CollectMaps_collectParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_CollectMaps_collectParams(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::nat_dec_eq(x_3, x_0);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectJP___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::array_get_size(x_0);
x_10 = lean::usize_of_nat(x_2);
x_11 = lean::usize_modn(x_10, x_9);
lean::dec(x_9);
x_13 = lean::array_uget(x_0, x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::array_uset(x_0, x_11, x_14);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_1, x_0, x_9);
x_11 = l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectJP___main___spec__5(x_2, x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_mul(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_4, x_6);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___main___spec__4(x_8, x_1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::nat_dec_eq(x_5, x_0);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_0, x_1, x_9);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_9);
return x_17;
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::array_get_size(x_5);
x_9 = lean::usize_of_nat(x_1);
x_10 = lean::usize_modn(x_9, x_8);
x_11 = lean::array_uget(x_5, x_10);
x_12 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_11);
x_17 = lean::array_uset(x_5, x_10, x_16);
x_18 = lean::nat_dec_le(x_14, x_8);
lean::dec(x_8);
if (x_18 == 0)
{
obj* x_21; 
lean::dec(x_7);
x_21 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(x_14, x_17);
return x_21;
}
else
{
obj* x_22; 
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_24 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_1, x_2, x_11);
x_25 = lean::array_uset(x_5, x_10, x_24);
if (lean::is_scalar(x_7)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_7;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
obj* l_Lean_IR_CollectMaps_collectJP___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_5, x_0, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_CollectMaps_collectJP(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_5, x_0, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_CollectMaps_collectFnBody___main(x_9, x_3);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_11;
goto _start;
}
}
}
obj* l_Lean_IR_CollectMaps_collectFnBody___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; uint8 x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_Lean_IR_CollectMaps_collectFnBody___main(x_7, x_1);
x_11 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
x_16 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_11, x_4, x_6);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
case 1:
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_0, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 3);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_Lean_IR_CollectMaps_collectFnBody___main(x_24, x_1);
x_28 = l_Lean_IR_CollectMaps_collectFnBody___main(x_22, x_27);
x_29 = lean::mk_nat_obj(0ul);
x_30 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_20, x_20, x_29, x_28);
x_31 = lean::cnstr_get(x_30, 0);
x_33 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_35 = x_30;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
x_36 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_33, x_18, x_20);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_31);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
case 10:
{
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_0, 2);
lean::inc(x_38);
lean::dec(x_0);
x_41 = lean::mk_nat_obj(0ul);
x_42 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_38, x_38, x_41, x_1);
lean::dec(x_38);
return x_42;
}
default:
{
obj* x_44; 
x_44 = lean::box(0);
x_2 = x_44;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_46; 
lean::dec(x_2);
x_46 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_46 == 0)
{
obj* x_47; 
x_47 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_47;
goto _start;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_CollectMaps_collectFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_CollectMaps_collectFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_CollectMaps_collectDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_Lean_IR_CollectMaps_collectFnBody___main(x_4, x_1);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_2, x_2, x_8, x_7);
lean::dec(x_2);
return x_9;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l_Lean_IR_CollectMaps_collectDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_CollectMaps_collectDecl___main(x_0, x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_mkVarJPMaps___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::mk_nat_obj(8ul);
x_1 = l_mkHashMapImp___rarg(x_0);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_IR_mkVarJPMaps(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_IR_mkVarJPMaps___closed__1;
x_2 = l_Lean_IR_CollectMaps_collectDecl___main(x_0, x_1);
return x_2;
}
}
obj* initialize_init_control_conditional(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_emitutil(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix = _init_l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix();
lean::mark_persistent(l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix);
 l_Lean_IR_mkVarJPMaps___closed__1 = _init_l_Lean_IR_mkVarJPMaps___closed__1();
lean::mark_persistent(l_Lean_IR_mkVarJPMaps___closed__1);
return w;
}
