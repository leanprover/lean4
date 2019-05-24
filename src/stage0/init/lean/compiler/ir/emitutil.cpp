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
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_IR_mkVarJPMaps___closed__1;
obj* l_Lean_IR_CollectUsedDecls_collect(obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(obj*, obj*);
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(obj*, uint8, obj*);
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(obj*, obj*);
obj* l_Lean_IR_CollectMaps_collectVar___main___boxed(obj*, obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
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
obj* l_Array_fget(obj*, obj*, obj*);
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
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = l_Lean_IR_AltCore_body___main(x_10);
lean::dec(x_10);
x_12 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_11, x_3, x_4);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_2);
x_19 = !lean::is_exclusive(x_12);
if (x_19 == 0)
{
obj* x_20; 
x_20 = lean::cnstr_get(x_12, 0);
lean::dec(x_20);
return x_12;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_12, 1);
lean::inc(x_21);
lean::dec(x_12);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_13);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_12; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
switch (lean::obj_tag(x_12)) {
case 6:
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_16 = l_Lean_Name_isPrefixOf___main(x_15, x_14);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = l_Lean_NameSet_contains(x_3, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::box(0);
lean::inc(x_14);
x_19 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_14, x_18);
x_20 = l_Lean_IR_findEnvDecl(x_2, x_14);
lean::dec(x_14);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
lean::dec(x_20);
x_1 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_23 = lean::cnstr_get(x_22, 2);
lean::inc(x_23);
lean::dec(x_22);
x_24 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_23, x_2, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_1 = x_13;
x_3 = x_27;
goto _start;
}
else
{
uint8 x_29; 
lean::dec(x_13);
x_29 = !lean::is_exclusive(x_24);
if (x_29 == 0)
{
obj* x_30; 
x_30 = lean::cnstr_get(x_24, 0);
lean::dec(x_30);
return x_24;
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_24, 1);
lean::inc(x_31);
lean::dec(x_24);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; 
lean::dec(x_22);
x_1 = x_13;
x_3 = x_19;
goto _start;
}
}
}
else
{
obj* x_34; 
lean::dec(x_14);
x_1 = x_13;
goto _start;
}
}
else
{
uint8 x_35; obj* x_36; obj* x_37; 
lean::dec(x_14);
lean::dec(x_13);
x_35 = 1;
x_36 = lean::box(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_3);
return x_37;
}
}
case 7:
{
obj* x_38; obj* x_39; obj* x_40; uint8 x_41; 
x_38 = lean::cnstr_get(x_1, 2);
lean::inc(x_38);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_12, 0);
lean::inc(x_39);
lean::dec(x_12);
x_40 = l_Lean_IR_UsesLeanNamespace_leanNameSpacePrefix;
x_41 = l_Lean_Name_isPrefixOf___main(x_40, x_39);
if (x_41 == 0)
{
uint8 x_42; 
x_42 = l_Lean_NameSet_contains(x_3, x_39);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::box(0);
lean::inc(x_39);
x_44 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_39, x_43);
x_45 = l_Lean_IR_findEnvDecl(x_2, x_39);
lean::dec(x_39);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; 
lean::dec(x_45);
x_1 = x_38;
x_3 = x_44;
goto _start;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_45, 0);
lean::inc(x_47);
lean::dec(x_45);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; uint8 x_51; 
x_48 = lean::cnstr_get(x_47, 2);
lean::inc(x_48);
lean::dec(x_47);
x_49 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_48, x_2, x_44);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::unbox(x_50);
if (x_51 == 0)
{
obj* x_52; obj* x_53; 
lean::dec(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
x_1 = x_38;
x_3 = x_52;
goto _start;
}
else
{
uint8 x_54; 
lean::dec(x_38);
x_54 = !lean::is_exclusive(x_49);
if (x_54 == 0)
{
obj* x_55; 
x_55 = lean::cnstr_get(x_49, 0);
lean::dec(x_55);
return x_49;
}
else
{
obj* x_56; obj* x_57; 
x_56 = lean::cnstr_get(x_49, 1);
lean::inc(x_56);
lean::dec(x_49);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_50);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; 
lean::dec(x_47);
x_1 = x_38;
x_3 = x_44;
goto _start;
}
}
}
else
{
obj* x_59; 
lean::dec(x_39);
x_1 = x_38;
goto _start;
}
}
else
{
uint8 x_60; obj* x_61; obj* x_62; 
lean::dec(x_39);
lean::dec(x_38);
x_60 = 1;
x_61 = lean::box(x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_3);
return x_62;
}
}
default: 
{
obj* x_63; obj* x_64; 
lean::dec(x_12);
x_63 = lean::cnstr_get(x_1, 2);
lean::inc(x_63);
lean::dec(x_1);
x_1 = x_63;
goto _start;
}
}
}
case 1:
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; uint8 x_69; 
x_65 = lean::cnstr_get(x_1, 2);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_1, 3);
lean::inc(x_66);
lean::dec(x_1);
x_67 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_65, x_2, x_3);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_69 = lean::unbox(x_68);
if (x_69 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_1 = x_66;
x_3 = x_70;
goto _start;
}
else
{
uint8 x_72; 
lean::dec(x_66);
x_72 = !lean::is_exclusive(x_67);
if (x_72 == 0)
{
obj* x_73; 
x_73 = lean::cnstr_get(x_67, 0);
lean::dec(x_73);
return x_67;
}
else
{
obj* x_74; obj* x_75; 
x_74 = lean::cnstr_get(x_67, 1);
lean::inc(x_74);
lean::dec(x_67);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_68);
lean::cnstr_set(x_75, 1, x_74);
return x_75;
}
}
}
case 10:
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = lean::cnstr_get(x_1, 2);
lean::inc(x_76);
lean::dec(x_1);
x_77 = lean::mk_nat_obj(0u);
x_78 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_76, x_77, x_2, x_3);
lean::dec(x_76);
return x_78;
}
default: 
{
obj* x_79; 
x_79 = lean::box(0);
x_4 = x_79;
goto block_11;
}
}
block_11:
{
uint8 x_5; 
lean::dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_6;
goto _start;
}
else
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
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_anyMAux___main___at_Lean_IR_UsesLeanNamespace_visitFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_UsesLeanNamespace_visitFnBody___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_UsesLeanNamespace_visitFnBody(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_usesLeanNamespace___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 2);
lean::inc(x_3);
lean::dec(x_2);
x_4 = lean::box(0);
x_5 = l_Lean_IR_UsesLeanNamespace_visitFnBody___main(x_3, x_1, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
else
{
uint8 x_7; obj* x_8; 
lean::dec(x_2);
x_7 = 0;
x_8 = lean::box(x_7);
return x_8;
}
}
}
obj* l_Lean_IR_usesLeanNamespace___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_usesLeanNamespace___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_usesLeanNamespace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_usesLeanNamespace___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_usesLeanNamespace___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_usesLeanNamespace(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_CollectUsedDecls_collect(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_1, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_2);
x_11 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_12 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_11, x_3);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_2 = x_10;
x_3 = x_13;
goto _start;
}
}
}
obj* l_Lean_IR_CollectUsedDecls_collectFnBody___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
switch (lean::obj_tag(x_10)) {
case 6:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean::box(0);
x_14 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_12, x_13);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
case 7:
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_1, 2);
lean::inc(x_16);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
x_18 = lean::box(0);
x_19 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_17, x_18);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
default: 
{
obj* x_21; obj* x_22; 
lean::dec(x_10);
x_21 = lean::cnstr_get(x_1, 2);
lean::inc(x_21);
lean::dec(x_1);
x_1 = x_21;
goto _start;
}
}
}
case 1:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_1, 2);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
lean::dec(x_1);
x_25 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_23, x_2);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_1 = x_24;
x_2 = x_26;
goto _start;
}
case 10:
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_1, 2);
lean::inc(x_28);
lean::dec(x_1);
x_29 = lean::mk_nat_obj(0u);
x_30 = l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_28, x_29, x_2);
lean::dec(x_28);
return x_30;
}
default: 
{
obj* x_31; 
x_31 = lean::box(0);
x_3 = x_31;
goto block_9;
}
}
block_9:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
obj* x_7; obj* x_8; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_CollectUsedDecls_collectFnBody___main___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_CollectUsedDecls_collectFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_collectUsedDecls(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_IR_CollectUsedDecls_collectFnBody___main(x_3, x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
uint8 x_7; 
x_2 = x_5;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::array_get_size(x_1);
x_7 = lean::usize_of_nat(x_4);
x_8 = lean::usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean::array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean::array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::array_get_size(x_1);
x_19 = lean::usize_of_nat(x_15);
x_20 = lean::usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean::array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean::array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___main___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectVar___main___spec__5(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectVar___main___spec__4(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
x_8 = lean::nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_1, x_2, x_7);
lean::cnstr_set(x_3, 2, x_9);
return x_3;
}
else
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_5);
x_10 = lean::box(x_2);
lean::cnstr_set(x_3, 1, x_10);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_11 = lean::cnstr_get(x_3, 0);
x_12 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::nat_dec_eq(x_11, x_1);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_1, x_2, x_13);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_12);
lean::dec(x_11);
x_17 = lean::box(x_2);
x_18 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_13);
return x_18;
}
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::array_get_size(x_6);
x_8 = lean::usize_of_nat(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; usize x_18; obj* x_19; uint8 x_20; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::box(x_3);
x_17 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_12);
x_18 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_19 = lean::array_uset(x_6, x_18, x_17);
x_20 = lean::nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_20 == 0)
{
obj* x_21; 
lean::free_heap_obj(x_1);
x_21 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(x_15, x_19);
return x_21;
}
else
{
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_22; usize x_23; obj* x_24; 
lean::dec(x_7);
x_22 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_2, x_3, x_12);
x_23 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_24 = lean::array_uset(x_6, x_23, x_22);
lean::cnstr_set(x_1, 1, x_24);
return x_1;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; usize x_28; usize x_29; obj* x_30; usize x_31; obj* x_32; uint8 x_33; 
x_25 = lean::cnstr_get(x_1, 0);
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_1);
x_27 = lean::array_get_size(x_26);
x_28 = lean::usize_of_nat(x_2);
x_29 = lean::usize_modn(x_28, x_27);
x_30 = lean::box_size_t(x_29);
x_31 = lean::unbox_size_t(x_30);
x_32 = lean::array_uget(x_26, x_31);
x_33 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(x_2, x_32);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; usize x_38; obj* x_39; uint8 x_40; 
x_34 = lean::mk_nat_obj(1u);
x_35 = lean::nat_add(x_25, x_34);
lean::dec(x_25);
x_36 = lean::box(x_3);
x_37 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_37, 0, x_2);
lean::cnstr_set(x_37, 1, x_36);
lean::cnstr_set(x_37, 2, x_32);
x_38 = lean::unbox_size_t(x_30);
lean::dec(x_30);
x_39 = lean::array_uset(x_26, x_38, x_37);
x_40 = lean::nat_dec_le(x_35, x_27);
lean::dec(x_27);
if (x_40 == 0)
{
obj* x_41; 
x_41 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectVar___main___spec__3(x_35, x_39);
return x_41;
}
else
{
obj* x_42; 
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_35);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
else
{
obj* x_43; usize x_44; obj* x_45; obj* x_46; 
lean::dec(x_27);
x_43 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_2, x_3, x_32);
x_44 = lean::unbox_size_t(x_30);
lean::dec(x_30);
x_45 = lean::array_uset(x_26, x_44, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_25);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
}
}
obj* l_Lean_IR_CollectMaps_collectVar___main(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_5, x_1, x_2);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_7, x_1, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
}
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectVar___main___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectVar___main___spec__6(x_1, x_4, x_3);
return x_5;
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_IR_CollectMaps_collectVar___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_IR_CollectMaps_collectVar___main(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Lean_IR_CollectMaps_collectVar(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_5, x_1, x_2);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_7, x_1, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
}
obj* l_Lean_IR_CollectMaps_collectVar___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_IR_CollectMaps_collectVar(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1 + 1);
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = !lean::is_exclusive(x_4);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_4, 0);
x_14 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_13, x_8, x_9);
lean::cnstr_set(x_4, 0, x_14);
x_3 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_4, 0);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_4);
x_18 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_16, x_8, x_9);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_3 = x_11;
x_4 = x_19;
goto _start;
}
}
}
}
obj* l_Lean_IR_CollectMaps_collectParams(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_CollectMaps_collectParams___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_CollectMaps_collectParams(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
uint8 x_7; 
x_2 = x_5;
goto _start;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectJP___main___spec__5(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::array_get_size(x_1);
x_7 = lean::usize_of_nat(x_4);
x_8 = lean::usize_modn(x_7, x_6);
lean::dec(x_6);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean::array_uget(x_1, x_10);
lean::cnstr_set(x_2, 2, x_11);
x_12 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_13 = lean::array_uset(x_1, x_12, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::array_get_size(x_1);
x_19 = lean::usize_of_nat(x_15);
x_20 = lean::usize_modn(x_19, x_18);
lean::dec(x_18);
x_21 = lean::box_size_t(x_20);
x_22 = lean::unbox_size_t(x_21);
x_23 = lean::array_uget(x_1, x_22);
x_24 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_26 = lean::array_uset(x_1, x_25, x_24);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___main___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldl___main___at_Lean_IR_CollectMaps_collectJP___main___spec__5(x_3, x_6);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_5, x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_CollectMaps_collectJP___main___spec__4(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
x_8 = lean::nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_1, x_2, x_7);
lean::cnstr_set(x_3, 2, x_9);
return x_3;
}
else
{
lean::dec(x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_1, x_2, x_12);
x_15 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_10);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::array_get_size(x_6);
x_8 = lean::usize_of_nat(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(x_2, x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_12);
x_17 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_18 = lean::array_uset(x_6, x_17, x_16);
x_19 = lean::nat_dec_le(x_15, x_7);
lean::dec(x_7);
if (x_19 == 0)
{
obj* x_20; 
lean::free_heap_obj(x_1);
x_20 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(x_15, x_18);
return x_20;
}
else
{
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_21; usize x_22; obj* x_23; 
lean::dec(x_7);
x_21 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_2, x_3, x_12);
x_22 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_23 = lean::array_uset(x_6, x_22, x_21);
lean::cnstr_set(x_1, 1, x_23);
return x_1;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; usize x_27; usize x_28; obj* x_29; usize x_30; obj* x_31; uint8 x_32; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_1);
x_26 = lean::array_get_size(x_25);
x_27 = lean::usize_of_nat(x_2);
x_28 = lean::usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean::array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(x_2, x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; usize x_36; obj* x_37; uint8 x_38; 
x_33 = lean::mk_nat_obj(1u);
x_34 = lean::nat_add(x_24, x_33);
lean::dec(x_24);
x_35 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_31);
x_36 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_37 = lean::array_uset(x_25, x_36, x_35);
x_38 = lean::nat_dec_le(x_34, x_26);
lean::dec(x_26);
if (x_38 == 0)
{
obj* x_39; 
x_39 = l_HashMapImp_expand___at_Lean_IR_CollectMaps_collectJP___main___spec__3(x_34, x_37);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
obj* x_41; usize x_42; obj* x_43; obj* x_44; 
lean::dec(x_26);
x_41 = l_AssocList_replace___main___at_Lean_IR_CollectMaps_collectJP___main___spec__6(x_2, x_3, x_31);
x_42 = lean::unbox_size_t(x_29);
lean::dec(x_29);
x_43 = lean::array_uset(x_25, x_42, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_24);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
obj* l_Lean_IR_CollectMaps_collectJP___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_5, x_1, x_2);
lean::cnstr_set(x_3, 1, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_8, x_1, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_CollectMaps_collectJP___main___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_IR_CollectMaps_collectJP(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_5, x_1, x_2);
lean::cnstr_set(x_3, 1, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_8, x_1, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_9 = l_Lean_IR_CollectMaps_collectFnBody___main(x_8, x_4);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
obj* l_Lean_IR_CollectMaps_collectFnBody___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::dec(x_1);
x_11 = l_Lean_IR_CollectMaps_collectFnBody___main(x_10, x_2);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_13, x_8, x_9);
lean::cnstr_set(x_11, 0, x_14);
return x_11;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_11, 0);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_11);
x_17 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectVar___main___spec__1(x_15, x_8, x_9);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
case 1:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_1, 2);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_1, 3);
lean::inc(x_22);
lean::dec(x_1);
x_23 = l_Lean_IR_CollectMaps_collectFnBody___main(x_22, x_2);
x_24 = l_Lean_IR_CollectMaps_collectFnBody___main(x_21, x_23);
x_25 = lean::mk_nat_obj(0u);
x_26 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_20, x_20, x_25, x_24);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 1);
x_29 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_28, x_19, x_20);
lean::cnstr_set(x_26, 1, x_29);
return x_26;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_26);
x_32 = l_HashMapImp_insert___at_Lean_IR_CollectMaps_collectJP___main___spec__1(x_31, x_19, x_20);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
case 10:
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_1, 2);
lean::inc(x_34);
lean::dec(x_1);
x_35 = lean::mk_nat_obj(0u);
x_36 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_34, x_34, x_35, x_2);
lean::dec(x_34);
return x_36;
}
default: 
{
obj* x_37; 
x_37 = lean::box(0);
x_3 = x_37;
goto block_7;
}
}
block_7:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_CollectMaps_collectFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_CollectMaps_collectFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_CollectMaps_collectDecl___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_IR_CollectMaps_collectFnBody___main(x_4, x_2);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_Lean_IR_CollectMaps_collectParams___spec__1(x_3, x_3, x_6, x_5);
lean::dec(x_3);
return x_7;
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Lean_IR_CollectMaps_collectDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_CollectMaps_collectDecl___main(x_1, x_2);
return x_3;
}
}
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_IR_mkVarJPMaps___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_mkVarJPMaps___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
lean::inc(x_2);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_IR_mkVarJPMaps(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_IR_mkVarJPMaps___closed__1;
x_3 = l_Lean_IR_CollectMaps_collectDecl___main(x_1, x_2);
return x_3;
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
