// Lean compiler output
// Module: init.lean.compiler.ir.normids
// Imports: init.control.reader init.control.conditional init.lean.compiler.ir.basic
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
obj* l_Lean_IR_MapVars_mapExpr(obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_IR_NormalizeIds_withVar___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkParams___boxed(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5___boxed(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkFnBody___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_MtoN(obj*);
obj* l_Lean_IR_FnBody_mapVars(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normVar___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkParams(obj*, obj*);
obj* l_Lean_IR_FnBody_replaceVar(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_uniqueIds(obj*);
obj* l_Lean_IR_NormalizeIds_withVar___boxed(obj*);
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkFnBody(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normDecl___main(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normVar(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normFnBody___main(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArg___main(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkDecl(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_replaceVar___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normDecl(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_NormalizeIds_normJP___boxed(obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normJP(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_NormalizeIds_normArgs(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(obj*, obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr___main(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normIndex___boxed(obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkDecl___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP(obj*);
obj* l_Lean_IR_NormalizeIds_MtoN___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normIndex(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_MtoN___boxed(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l_Lean_IR_MapVars_mapFnBody(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArg(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkId(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapExpr___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withVar(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::nat_dec_lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = lean::nat_dec_lt(x_5, x_1);
if (x_14 == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_9);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_7);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = lean::nat_dec_lt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::nat_dec_lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = lean::nat_dec_lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = lean::nat_dec_lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_Lean_IR_UniqueIds_checkId(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_1, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(x_1, x_0, x_4);
x_6 = 1;
x_7 = lean::box(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8 x_11; obj* x_12; obj* x_13; 
lean::dec(x_0);
lean::dec(x_3);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
return x_13;
}
}
}
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_14; obj* x_15; uint8 x_17; 
x_10 = lean::array_fget(x_0, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_14 = l_Lean_IR_UniqueIds_checkId(x_11, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_19; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; 
lean::dec(x_1);
x_19 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_21 = x_14;
} else {
 lean::inc(x_19);
 lean::dec(x_14);
 x_21 = lean::box(0);
}
x_22 = 1;
x_23 = lean::box(x_22);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_19);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
lean::dec(x_14);
x_28 = lean::mk_nat_obj(1ul);
x_29 = lean::nat_add(x_1, x_28);
lean::dec(x_1);
x_1 = x_29;
x_2 = x_25;
goto _start;
}
}
}
}
obj* l_Lean_IR_UniqueIds_checkParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_6; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_0, x_2, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::unbox(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
} else {
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 1;
x_11 = lean::box(x_10);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = 0;
x_17 = lean::box(x_16);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_UniqueIds_checkParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_UniqueIds_checkParams(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; uint8 x_16; 
x_10 = lean::array_fget(x_0, x_1);
x_11 = l_Lean_IR_AltCore_body___main(x_10);
lean::dec(x_10);
x_13 = l_Lean_IR_UniqueIds_checkFnBody___main(x_11, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::unbox(x_14);
if (x_16 == 0)
{
obj* x_18; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
lean::dec(x_1);
x_18 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_20 = x_13;
} else {
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = 1;
x_22 = lean::box(x_21);
if (lean::is_scalar(x_20)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_20;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_18);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_13, 1);
lean::inc(x_24);
lean::dec(x_13);
x_27 = lean::mk_nat_obj(1ul);
x_28 = lean::nat_add(x_1, x_27);
lean::dec(x_1);
x_1 = x_28;
x_2 = x_24;
goto _start;
}
}
}
}
obj* l_Lean_IR_UniqueIds_checkFnBody___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; uint8 x_12; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_Lean_IR_UniqueIds_checkId(x_4, x_1);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::unbox(x_10);
if (x_12 == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_6);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_9, 1);
lean::inc(x_18);
lean::dec(x_9);
x_0 = x_6;
x_1 = x_18;
goto _start;
}
}
case 1:
{
obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; uint8 x_32; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 3);
lean::inc(x_26);
lean::dec(x_0);
x_29 = l_Lean_IR_UniqueIds_checkId(x_22, x_1);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::unbox(x_30);
if (x_32 == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_26);
lean::dec(x_24);
x_35 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_37 = x_29;
} else {
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_30);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_44; uint8 x_46; 
x_39 = lean::cnstr_get(x_29, 1);
lean::inc(x_39);
lean::dec(x_29);
x_42 = l_Lean_IR_UniqueIds_checkParams(x_24, x_39);
lean::dec(x_24);
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
x_46 = lean::unbox(x_44);
if (x_46 == 0)
{
obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_26);
x_48 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_50 = x_42;
} else {
 lean::inc(x_48);
 lean::dec(x_42);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_44);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_42, 1);
lean::inc(x_52);
lean::dec(x_42);
x_0 = x_26;
x_1 = x_52;
goto _start;
}
}
}
case 10:
{
obj* x_56; obj* x_59; obj* x_60; obj* x_62; uint8 x_64; 
x_56 = lean::cnstr_get(x_0, 2);
lean::inc(x_56);
lean::dec(x_0);
x_59 = lean::mk_nat_obj(0ul);
x_60 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_56, x_59, x_1);
lean::dec(x_56);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
x_64 = lean::unbox(x_62);
if (x_64 == 0)
{
obj* x_65; obj* x_67; uint8 x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = 1;
x_69 = lean::box(x_68);
if (lean::is_scalar(x_67)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_67;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
return x_70;
}
else
{
obj* x_71; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_73 = x_60;
} else {
 lean::inc(x_71);
 lean::dec(x_60);
 x_73 = lean::box(0);
}
x_74 = 0;
x_75 = lean::box(x_74);
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_71);
return x_76;
}
}
default:
{
obj* x_77; 
x_77 = lean::box(0);
x_2 = x_77;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_79; 
lean::dec(x_2);
x_79 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_79 == 0)
{
obj* x_80; 
x_80 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_80;
goto _start;
}
else
{
uint8 x_84; obj* x_85; obj* x_86; 
lean::dec(x_0);
x_84 = 1;
x_85 = lean::box(x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_1);
return x_86;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_UniqueIds_checkFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_UniqueIds_checkFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_UniqueIds_checkDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; uint8 x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_Lean_IR_UniqueIds_checkParams(x_2, x_1);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_11 = lean::unbox(x_9);
if (x_11 == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_4);
x_13 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
lean::dec(x_7);
x_20 = l_Lean_IR_UniqueIds_checkFnBody___main(x_4, x_17);
return x_20;
}
}
else
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = l_Lean_IR_UniqueIds_checkParams(x_21, x_1);
lean::dec(x_21);
return x_24;
}
}
}
obj* l_Lean_IR_UniqueIds_checkDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_UniqueIds_checkDecl___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_uniqueIds(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_IR_UniqueIds_checkDecl___main(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normIndex(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
return x_4;
}
}
}
obj* l_Lean_IR_NormalizeIds_normIndex___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normIndex(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_normVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normIndex(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_normVar___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normVar(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_normJP(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normIndex(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_normJP___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normJP(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_normArg___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = l_Lean_IR_NormalizeIds_normIndex(x_2, x_1);
lean::dec(x_2);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_5);
return x_7;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_Lean_IR_NormalizeIds_normArg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normArg___main(x_0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = lean::box(1);
x_10 = lean::array_fset(x_2, x_1, x_9);
lean::inc(x_0);
x_12 = l_Lean_IR_NormalizeIds_normArg___main(x_8, x_0);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_1, x_13);
x_15 = lean::array_fset(x_10, x_1, x_12);
lean::dec(x_1);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Lean_IR_NormalizeIds_normArgs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normExpr___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::mk_nat_obj(0ul);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_7, x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
case 1:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
x_10 = lean::cnstr_get(x_0, 0);
x_12 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_14 = x_0;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = l_Lean_IR_NormalizeIds_normIndex(x_12, x_1);
lean::dec(x_12);
if (lean::is_scalar(x_14)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_14;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_15);
return x_17;
}
case 2:
{
obj* x_18; obj* x_20; uint8 x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_18 = lean::cnstr_get(x_0, 0);
x_20 = lean::cnstr_get(x_0, 1);
x_22 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_23 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_25 = x_0;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_23);
 lean::dec(x_0);
 x_25 = lean::box(0);
}
lean::inc(x_1);
x_27 = l_Lean_IR_NormalizeIds_normIndex(x_18, x_1);
lean::dec(x_18);
x_29 = lean::mk_nat_obj(0ul);
x_30 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_29, x_23);
if (lean::is_scalar(x_25)) {
 x_31 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_31 = x_25;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_20);
lean::cnstr_set(x_31, 2, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*3, x_22);
x_32 = x_31;
return x_32;
}
case 3:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; 
x_33 = lean::cnstr_get(x_0, 0);
x_35 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_37 = x_0;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_0);
 x_37 = lean::box(0);
}
x_38 = l_Lean_IR_NormalizeIds_normIndex(x_35, x_1);
lean::dec(x_35);
if (lean::is_scalar(x_37)) {
 x_40 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_40 = x_37;
}
lean::cnstr_set(x_40, 0, x_33);
lean::cnstr_set(x_40, 1, x_38);
return x_40;
}
case 4:
{
obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_48; 
x_41 = lean::cnstr_get(x_0, 0);
x_43 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_45 = x_0;
} else {
 lean::inc(x_41);
 lean::inc(x_43);
 lean::dec(x_0);
 x_45 = lean::box(0);
}
x_46 = l_Lean_IR_NormalizeIds_normIndex(x_43, x_1);
lean::dec(x_43);
if (lean::is_scalar(x_45)) {
 x_48 = lean::alloc_cnstr(4, 2, 0);
} else {
 x_48 = x_45;
}
lean::cnstr_set(x_48, 0, x_41);
lean::cnstr_set(x_48, 1, x_46);
return x_48;
}
case 5:
{
obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; 
x_49 = lean::cnstr_get(x_0, 0);
x_51 = lean::cnstr_get(x_0, 1);
x_53 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_55 = x_0;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_0);
 x_55 = lean::box(0);
}
x_56 = l_Lean_IR_NormalizeIds_normIndex(x_53, x_1);
lean::dec(x_53);
if (lean::is_scalar(x_55)) {
 x_58 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_58 = x_55;
}
lean::cnstr_set(x_58, 0, x_49);
lean::cnstr_set(x_58, 1, x_51);
lean::cnstr_set(x_58, 2, x_56);
return x_58;
}
case 6:
{
obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_59 = lean::cnstr_get(x_0, 0);
x_61 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_63 = x_0;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_0);
 x_63 = lean::box(0);
}
x_64 = lean::mk_nat_obj(0ul);
x_65 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_64, x_61);
if (lean::is_scalar(x_63)) {
 x_66 = lean::alloc_cnstr(6, 2, 0);
} else {
 x_66 = x_63;
}
lean::cnstr_set(x_66, 0, x_59);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
case 7:
{
obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_67 = lean::cnstr_get(x_0, 0);
x_69 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_71 = x_0;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::dec(x_0);
 x_71 = lean::box(0);
}
x_72 = lean::mk_nat_obj(0ul);
x_73 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_72, x_69);
if (lean::is_scalar(x_71)) {
 x_74 = lean::alloc_cnstr(7, 2, 0);
} else {
 x_74 = x_71;
}
lean::cnstr_set(x_74, 0, x_67);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
case 8:
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
x_75 = lean::cnstr_get(x_0, 0);
x_77 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_79 = x_0;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_0);
 x_79 = lean::box(0);
}
lean::inc(x_1);
x_81 = l_Lean_IR_NormalizeIds_normIndex(x_75, x_1);
lean::dec(x_75);
x_83 = lean::mk_nat_obj(0ul);
x_84 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_83, x_77);
if (lean::is_scalar(x_79)) {
 x_85 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_85 = x_79;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set(x_85, 1, x_84);
return x_85;
}
case 9:
{
uint8 x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_93; 
x_86 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_87 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_89 = x_0;
} else {
 lean::inc(x_87);
 lean::dec(x_0);
 x_89 = lean::box(0);
}
x_90 = l_Lean_IR_NormalizeIds_normIndex(x_87, x_1);
lean::dec(x_87);
if (lean::is_scalar(x_89)) {
 x_92 = lean::alloc_cnstr(9, 1, 1);
} else {
 x_92 = x_89;
}
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_86);
x_93 = x_92;
return x_93;
}
case 10:
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; 
x_94 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_96 = x_0;
} else {
 lean::inc(x_94);
 lean::dec(x_0);
 x_96 = lean::box(0);
}
x_97 = l_Lean_IR_NormalizeIds_normIndex(x_94, x_1);
lean::dec(x_94);
if (lean::is_scalar(x_96)) {
 x_99 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_99 = x_96;
}
lean::cnstr_set(x_99, 0, x_97);
return x_99;
}
case 11:
{
lean::dec(x_1);
return x_0;
}
case 12:
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; 
x_101 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_103 = x_0;
} else {
 lean::inc(x_101);
 lean::dec(x_0);
 x_103 = lean::box(0);
}
x_104 = l_Lean_IR_NormalizeIds_normIndex(x_101, x_1);
lean::dec(x_101);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(12, 1, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_104);
return x_106;
}
default:
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; 
x_107 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_109 = x_0;
} else {
 lean::inc(x_107);
 lean::dec(x_0);
 x_109 = lean::box(0);
}
x_110 = l_Lean_IR_NormalizeIds_normIndex(x_107, x_1);
lean::dec(x_107);
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(13, 1, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_110);
return x_112;
}
}
}
}
obj* l_Lean_IR_NormalizeIds_normExpr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_NormalizeIds_normExpr___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_withVar___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
lean::inc(x_3);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_0, x_3);
x_8 = lean::apply_3(x_1, x_3, x_7, x_5);
return x_8;
}
}
obj* l_Lean_IR_NormalizeIds_withVar(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withVar___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_withVar___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_NormalizeIds_withVar(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_withJP___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
lean::inc(x_3);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_0, x_3);
x_8 = lean::apply_3(x_1, x_3, x_7, x_5);
return x_8;
}
}
obj* l_Lean_IR_NormalizeIds_withJP(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withJP___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_withJP___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_NormalizeIds_withJP(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::nat_add(x_4, x_11);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_15, x_4);
x_2 = x_12;
x_3 = x_18;
x_4 = x_14;
goto _start;
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1() {
_start:
{
obj* x_0; uint8 x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = 0;
x_2 = 7;
x_3 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_1);
x_4 = x_3;
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_2);
x_5 = x_4;
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; uint8 x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
x_14 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1 + 1);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_0);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 1, 2);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_13);
x_20 = x_19;
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_14);
x_21 = x_20;
x_22 = lean::mk_nat_obj(1ul);
x_23 = lean::nat_add(x_1, x_22);
x_24 = lean::array_fset(x_10, x_1, x_21);
lean::dec(x_1);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
}
obj* l_Lean_IR_NormalizeIds_withParams___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_0, x_0, x_4, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
lean::inc(x_6);
x_12 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(x_6, x_4, x_0);
x_13 = lean::apply_3(x_1, x_12, x_6, x_8);
return x_13;
}
}
obj* l_Lean_IR_NormalizeIds_withParams(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withParams___rarg), 4, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_NormalizeIds_withParams___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_NormalizeIds_withParams(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_MtoN___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_MtoN(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_MtoN___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_MtoN___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_NormalizeIds_MtoN(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::nat_add(x_4, x_11);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_15, x_4);
x_2 = x_12;
x_3 = x_18;
x_4 = x_14;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; uint8 x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
x_14 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1 + 1);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_0);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 1, 2);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_13);
x_20 = x_19;
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_14);
x_21 = x_20;
x_22 = lean::mk_nat_obj(1ul);
x_23 = lean::nat_add(x_1, x_22);
x_24 = lean::array_fset(x_10, x_1, x_21);
lean::dec(x_1);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(13);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_1, x_0);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_12 = lean::array_fset(x_1, x_0, x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
lean::inc(x_2);
x_19 = l_Lean_IR_NormalizeIds_normFnBody___main(x_15, x_2, x_3);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_20);
x_26 = lean::mk_nat_obj(1ul);
x_27 = lean::nat_add(x_0, x_26);
x_28 = lean::array_fset(x_12, x_0, x_25);
lean::dec(x_0);
x_0 = x_27;
x_1 = x_28;
x_3 = x_22;
goto _start;
}
else
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_31 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_33 = x_10;
} else {
 lean::inc(x_31);
 lean::dec(x_10);
 x_33 = lean::box(0);
}
lean::inc(x_2);
x_35 = l_Lean_IR_NormalizeIds_normFnBody___main(x_31, x_2, x_3);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
if (lean::is_scalar(x_33)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_33;
}
lean::cnstr_set(x_41, 0, x_36);
x_42 = lean::mk_nat_obj(1ul);
x_43 = lean::nat_add(x_0, x_42);
x_44 = lean::array_fset(x_12, x_0, x_41);
lean::dec(x_0);
x_0 = x_43;
x_1 = x_44;
x_3 = x_38;
goto _start;
}
}
}
}
obj* l_Lean_IR_NormalizeIds_normFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_10 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
lean::inc(x_1);
x_12 = l_Lean_IR_NormalizeIds_normExpr___main(x_6, x_1);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::inc(x_2);
x_16 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_3, x_2);
x_17 = l_Lean_IR_NormalizeIds_normFnBody___main(x_8, x_16, x_14);
x_18 = lean::cnstr_get(x_17, 0);
x_20 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_23 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_23 = x_10;
}
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_12);
lean::cnstr_set(x_23, 2, x_18);
lean::cnstr_set_scalar(x_23, sizeof(void*)*3, x_5);
x_24 = x_23;
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_20);
return x_25;
}
case 1:
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_26 = lean::cnstr_get(x_0, 0);
x_28 = lean::cnstr_get(x_0, 1);
x_30 = lean::cnstr_get(x_0, 2);
x_32 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_34 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_0);
 x_34 = lean::box(0);
}
x_35 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_37 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_28, x_28, x_35, x_1, x_2);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
lean::inc(x_38);
x_44 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_38, x_35, x_28);
x_45 = l_Lean_IR_NormalizeIds_normFnBody___main(x_30, x_38, x_40);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = lean::mk_nat_obj(1ul);
x_52 = lean::nat_add(x_48, x_51);
lean::inc(x_48);
x_54 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_26, x_48);
x_55 = l_Lean_IR_NormalizeIds_normFnBody___main(x_32, x_54, x_52);
x_56 = lean::cnstr_get(x_55, 0);
x_58 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_60 = x_55;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_55);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_61 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_61 = x_34;
}
lean::cnstr_set(x_61, 0, x_48);
lean::cnstr_set(x_61, 1, x_44);
lean::cnstr_set(x_61, 2, x_46);
lean::cnstr_set(x_61, 3, x_56);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_58);
return x_62;
}
case 2:
{
obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
x_63 = lean::cnstr_get(x_0, 0);
x_65 = lean::cnstr_get(x_0, 1);
x_67 = lean::cnstr_get(x_0, 2);
x_69 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_71 = x_0;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::dec(x_0);
 x_71 = lean::box(0);
}
lean::inc(x_1);
x_73 = l_Lean_IR_NormalizeIds_normIndex(x_63, x_1);
lean::dec(x_63);
lean::inc(x_1);
x_76 = l_Lean_IR_NormalizeIds_normArg___main(x_67, x_1);
x_77 = l_Lean_IR_NormalizeIds_normFnBody___main(x_69, x_1, x_2);
x_78 = lean::cnstr_get(x_77, 0);
x_80 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 x_82 = x_77;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_77);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_83 = x_71;
}
lean::cnstr_set(x_83, 0, x_73);
lean::cnstr_set(x_83, 1, x_65);
lean::cnstr_set(x_83, 2, x_76);
lean::cnstr_set(x_83, 3, x_78);
if (lean::is_scalar(x_82)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_82;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_80);
return x_84;
}
case 3:
{
obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
x_85 = lean::cnstr_get(x_0, 0);
x_87 = lean::cnstr_get(x_0, 1);
x_89 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_91 = x_0;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_0);
 x_91 = lean::box(0);
}
lean::inc(x_1);
x_93 = l_Lean_IR_NormalizeIds_normIndex(x_85, x_1);
lean::dec(x_85);
x_95 = l_Lean_IR_NormalizeIds_normFnBody___main(x_89, x_1, x_2);
x_96 = lean::cnstr_get(x_95, 0);
x_98 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 x_100 = x_95;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_101 = lean::alloc_cnstr(3, 3, 0);
} else {
 x_101 = x_91;
}
lean::cnstr_set(x_101, 0, x_93);
lean::cnstr_set(x_101, 1, x_87);
lean::cnstr_set(x_101, 2, x_96);
if (lean::is_scalar(x_100)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_100;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_98);
return x_102;
}
case 4:
{
obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_116; obj* x_118; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_125; 
x_103 = lean::cnstr_get(x_0, 0);
x_105 = lean::cnstr_get(x_0, 1);
x_107 = lean::cnstr_get(x_0, 2);
x_109 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_111 = x_0;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::inc(x_109);
 lean::dec(x_0);
 x_111 = lean::box(0);
}
lean::inc(x_1);
x_113 = l_Lean_IR_NormalizeIds_normIndex(x_103, x_1);
lean::dec(x_103);
lean::inc(x_1);
x_116 = l_Lean_IR_NormalizeIds_normIndex(x_107, x_1);
lean::dec(x_107);
x_118 = l_Lean_IR_NormalizeIds_normFnBody___main(x_109, x_1, x_2);
x_119 = lean::cnstr_get(x_118, 0);
x_121 = lean::cnstr_get(x_118, 1);
if (lean::is_exclusive(x_118)) {
 x_123 = x_118;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_118);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_124 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_124 = x_111;
}
lean::cnstr_set(x_124, 0, x_113);
lean::cnstr_set(x_124, 1, x_105);
lean::cnstr_set(x_124, 2, x_116);
lean::cnstr_set(x_124, 3, x_119);
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_121);
return x_125;
}
case 5:
{
obj* x_126; obj* x_128; obj* x_130; obj* x_132; uint8 x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_126 = lean::cnstr_get(x_0, 0);
x_128 = lean::cnstr_get(x_0, 1);
x_130 = lean::cnstr_get(x_0, 2);
x_132 = lean::cnstr_get(x_0, 3);
x_134 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
x_135 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 x_137 = x_0;
} else {
 lean::inc(x_126);
 lean::inc(x_128);
 lean::inc(x_130);
 lean::inc(x_132);
 lean::inc(x_135);
 lean::dec(x_0);
 x_137 = lean::box(0);
}
lean::inc(x_1);
x_139 = l_Lean_IR_NormalizeIds_normIndex(x_126, x_1);
lean::dec(x_126);
lean::inc(x_1);
x_142 = l_Lean_IR_NormalizeIds_normIndex(x_132, x_1);
lean::dec(x_132);
x_144 = l_Lean_IR_NormalizeIds_normFnBody___main(x_135, x_1, x_2);
x_145 = lean::cnstr_get(x_144, 0);
x_147 = lean::cnstr_get(x_144, 1);
if (lean::is_exclusive(x_144)) {
 x_149 = x_144;
} else {
 lean::inc(x_145);
 lean::inc(x_147);
 lean::dec(x_144);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_150 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_150 = x_137;
}
lean::cnstr_set(x_150, 0, x_139);
lean::cnstr_set(x_150, 1, x_128);
lean::cnstr_set(x_150, 2, x_130);
lean::cnstr_set(x_150, 3, x_142);
lean::cnstr_set(x_150, 4, x_145);
lean::cnstr_set_scalar(x_150, sizeof(void*)*5, x_134);
x_151 = x_150;
if (lean::is_scalar(x_149)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_149;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_147);
return x_152;
}
case 6:
{
obj* x_153; obj* x_155; uint8 x_157; obj* x_158; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_153 = lean::cnstr_get(x_0, 0);
x_155 = lean::cnstr_get(x_0, 1);
x_157 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_158 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_160 = x_0;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::inc(x_158);
 lean::dec(x_0);
 x_160 = lean::box(0);
}
lean::inc(x_1);
x_162 = l_Lean_IR_NormalizeIds_normIndex(x_153, x_1);
lean::dec(x_153);
x_164 = l_Lean_IR_NormalizeIds_normFnBody___main(x_158, x_1, x_2);
x_165 = lean::cnstr_get(x_164, 0);
x_167 = lean::cnstr_get(x_164, 1);
if (lean::is_exclusive(x_164)) {
 x_169 = x_164;
} else {
 lean::inc(x_165);
 lean::inc(x_167);
 lean::dec(x_164);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_170 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_170 = x_160;
}
lean::cnstr_set(x_170, 0, x_162);
lean::cnstr_set(x_170, 1, x_155);
lean::cnstr_set(x_170, 2, x_165);
lean::cnstr_set_scalar(x_170, sizeof(void*)*3, x_157);
x_171 = x_170;
if (lean::is_scalar(x_169)) {
 x_172 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_172 = x_169;
}
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_167);
return x_172;
}
case 7:
{
obj* x_173; obj* x_175; uint8 x_177; obj* x_178; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
x_173 = lean::cnstr_get(x_0, 0);
x_175 = lean::cnstr_get(x_0, 1);
x_177 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_178 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_180 = x_0;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::inc(x_178);
 lean::dec(x_0);
 x_180 = lean::box(0);
}
lean::inc(x_1);
x_182 = l_Lean_IR_NormalizeIds_normIndex(x_173, x_1);
lean::dec(x_173);
x_184 = l_Lean_IR_NormalizeIds_normFnBody___main(x_178, x_1, x_2);
x_185 = lean::cnstr_get(x_184, 0);
x_187 = lean::cnstr_get(x_184, 1);
if (lean::is_exclusive(x_184)) {
 x_189 = x_184;
} else {
 lean::inc(x_185);
 lean::inc(x_187);
 lean::dec(x_184);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_190 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_190 = x_180;
}
lean::cnstr_set(x_190, 0, x_182);
lean::cnstr_set(x_190, 1, x_175);
lean::cnstr_set(x_190, 2, x_185);
lean::cnstr_set_scalar(x_190, sizeof(void*)*3, x_177);
x_191 = x_190;
if (lean::is_scalar(x_189)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_189;
}
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_187);
return x_192;
}
case 8:
{
obj* x_193; obj* x_195; obj* x_197; obj* x_199; obj* x_201; obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_208; 
x_193 = lean::cnstr_get(x_0, 0);
x_195 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_197 = x_0;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_0);
 x_197 = lean::box(0);
}
lean::inc(x_1);
x_199 = l_Lean_IR_NormalizeIds_normIndex(x_193, x_1);
lean::dec(x_193);
x_201 = l_Lean_IR_NormalizeIds_normFnBody___main(x_195, x_1, x_2);
x_202 = lean::cnstr_get(x_201, 0);
x_204 = lean::cnstr_get(x_201, 1);
if (lean::is_exclusive(x_201)) {
 x_206 = x_201;
} else {
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_201);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_207 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_207 = x_197;
}
lean::cnstr_set(x_207, 0, x_199);
lean::cnstr_set(x_207, 1, x_202);
if (lean::is_scalar(x_206)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_206;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_204);
return x_208;
}
case 9:
{
obj* x_209; obj* x_211; obj* x_213; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_221; 
x_209 = lean::cnstr_get(x_0, 0);
x_211 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_213 = x_0;
} else {
 lean::inc(x_209);
 lean::inc(x_211);
 lean::dec(x_0);
 x_213 = lean::box(0);
}
x_214 = l_Lean_IR_NormalizeIds_normFnBody___main(x_211, x_1, x_2);
x_215 = lean::cnstr_get(x_214, 0);
x_217 = lean::cnstr_get(x_214, 1);
if (lean::is_exclusive(x_214)) {
 x_219 = x_214;
} else {
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_214);
 x_219 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_220 = lean::alloc_cnstr(9, 2, 0);
} else {
 x_220 = x_213;
}
lean::cnstr_set(x_220, 0, x_209);
lean::cnstr_set(x_220, 1, x_215);
if (lean::is_scalar(x_219)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_219;
}
lean::cnstr_set(x_221, 0, x_220);
lean::cnstr_set(x_221, 1, x_217);
return x_221;
}
case 10:
{
obj* x_222; obj* x_224; obj* x_226; obj* x_228; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_236; obj* x_238; obj* x_239; obj* x_240; 
x_222 = lean::cnstr_get(x_0, 0);
x_224 = lean::cnstr_get(x_0, 1);
x_226 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_228 = x_0;
} else {
 lean::inc(x_222);
 lean::inc(x_224);
 lean::inc(x_226);
 lean::dec(x_0);
 x_228 = lean::box(0);
}
lean::inc(x_1);
x_230 = l_Lean_IR_NormalizeIds_normIndex(x_224, x_1);
lean::dec(x_224);
x_232 = lean::mk_nat_obj(0ul);
x_233 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(x_232, x_226, x_1, x_2);
x_234 = lean::cnstr_get(x_233, 0);
x_236 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 x_238 = x_233;
} else {
 lean::inc(x_234);
 lean::inc(x_236);
 lean::dec(x_233);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_239 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_239 = x_228;
}
lean::cnstr_set(x_239, 0, x_222);
lean::cnstr_set(x_239, 1, x_230);
lean::cnstr_set(x_239, 2, x_234);
if (lean::is_scalar(x_238)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_238;
}
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_236);
return x_240;
}
case 11:
{
obj* x_241; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
x_241 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_243 = x_0;
} else {
 lean::inc(x_241);
 lean::dec(x_0);
 x_243 = lean::box(0);
}
x_244 = l_Lean_IR_NormalizeIds_normArg___main(x_241, x_1);
if (lean::is_scalar(x_243)) {
 x_245 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_245 = x_243;
}
lean::cnstr_set(x_245, 0, x_244);
x_246 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_246, 0, x_245);
lean::cnstr_set(x_246, 1, x_2);
return x_246;
}
case 12:
{
obj* x_247; obj* x_249; obj* x_251; obj* x_253; obj* x_255; obj* x_256; obj* x_257; obj* x_258; 
x_247 = lean::cnstr_get(x_0, 0);
x_249 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_251 = x_0;
} else {
 lean::inc(x_247);
 lean::inc(x_249);
 lean::dec(x_0);
 x_251 = lean::box(0);
}
lean::inc(x_1);
x_253 = l_Lean_IR_NormalizeIds_normIndex(x_247, x_1);
lean::dec(x_247);
x_255 = lean::mk_nat_obj(0ul);
x_256 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_255, x_249);
if (lean::is_scalar(x_251)) {
 x_257 = lean::alloc_cnstr(12, 2, 0);
} else {
 x_257 = x_251;
}
lean::cnstr_set(x_257, 0, x_253);
lean::cnstr_set(x_257, 1, x_256);
x_258 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_258, 0, x_257);
lean::cnstr_set(x_258, 1, x_2);
return x_258;
}
default:
{
obj* x_260; 
lean::dec(x_1);
x_260 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_260, 0, x_0);
lean::cnstr_set(x_260, 1, x_2);
return x_260;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_NormalizeIds_normFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_18; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_14 = lean::nat_add(x_4, x_11);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_15, x_4);
x_2 = x_12;
x_3 = x_18;
x_4 = x_14;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; uint8 x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
x_14 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1 + 1);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = l_Lean_IR_NormalizeIds_normIndex(x_11, x_0);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 1, 2);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_13);
x_20 = x_19;
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_14);
x_21 = x_20;
x_22 = lean::mk_nat_obj(1ul);
x_23 = lean::nat_add(x_1, x_22);
x_24 = lean::array_fset(x_10, x_1, x_21);
lean::dec(x_1);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
}
obj* l_Lean_IR_NormalizeIds_normDecl___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; uint8 x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_8 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_10 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
x_11 = lean::mk_nat_obj(0ul);
x_12 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(x_5, x_5, x_11, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
lean::inc(x_13);
x_19 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(x_13, x_11, x_5);
x_20 = l_Lean_IR_NormalizeIds_normFnBody___main(x_8, x_13, x_15);
x_21 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_26 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_26 = x_10;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_19);
lean::cnstr_set(x_26, 2, x_21);
lean::cnstr_set_scalar(x_26, sizeof(void*)*3, x_7);
x_27 = x_26;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_23);
return x_28;
}
else
{
obj* x_30; 
lean::dec(x_1);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_0);
lean::cnstr_set(x_30, 1, x_2);
return x_30;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_NormalizeIds_normDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normDecl___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Decl_normalizeIds(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = l_Lean_IR_NormalizeIds_normDecl___main(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArg___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l_Lean_IR_MapVars_mapArg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::apply_1(x_0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = lean::box(1);
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_1, x_11);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = lean::apply_1(x_0, x_13);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::array_fset(x_10, x_1, x_18);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_19;
goto _start;
}
else
{
obj* x_22; 
x_22 = lean::array_fset(x_10, x_1, x_8);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_22;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::mk_nat_obj(0ul);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_7, x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
case 1:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_14 = x_1;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::apply_1(x_0, x_12);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
case 2:
{
obj* x_17; obj* x_19; uint8 x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_17 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_21 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_22 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_24 = x_1;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_22);
 lean::dec(x_1);
 x_24 = lean::box(0);
}
lean::inc(x_0);
x_26 = lean::apply_1(x_0, x_17);
x_27 = lean::mk_nat_obj(0ul);
x_28 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_27, x_22);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_19);
lean::cnstr_set(x_29, 2, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*3, x_21);
x_30 = x_29;
return x_30;
}
case 3:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_35 = x_1;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_1);
 x_35 = lean::box(0);
}
x_36 = lean::apply_1(x_0, x_33);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_31);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
case 4:
{
obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
x_38 = lean::cnstr_get(x_1, 0);
x_40 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_42 = x_1;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_1);
 x_42 = lean::box(0);
}
x_43 = lean::apply_1(x_0, x_40);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(4, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
case 5:
{
obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_45 = lean::cnstr_get(x_1, 0);
x_47 = lean::cnstr_get(x_1, 1);
x_49 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_51 = x_1;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_1);
 x_51 = lean::box(0);
}
x_52 = lean::apply_1(x_0, x_49);
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_45);
lean::cnstr_set(x_53, 1, x_47);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
case 6:
{
obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_1, 0);
x_56 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_58 = x_1;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_1);
 x_58 = lean::box(0);
}
x_59 = lean::mk_nat_obj(0ul);
x_60 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_59, x_56);
if (lean::is_scalar(x_58)) {
 x_61 = lean::alloc_cnstr(6, 2, 0);
} else {
 x_61 = x_58;
}
lean::cnstr_set(x_61, 0, x_54);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
case 7:
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_1, 0);
x_64 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_66 = x_1;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_1);
 x_66 = lean::box(0);
}
x_67 = lean::mk_nat_obj(0ul);
x_68 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_67, x_64);
if (lean::is_scalar(x_66)) {
 x_69 = lean::alloc_cnstr(7, 2, 0);
} else {
 x_69 = x_66;
}
lean::cnstr_set(x_69, 0, x_62);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
}
case 8:
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_1, 0);
x_72 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_74 = x_1;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_1);
 x_74 = lean::box(0);
}
lean::inc(x_0);
x_76 = lean::apply_1(x_0, x_70);
x_77 = lean::mk_nat_obj(0ul);
x_78 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_77, x_72);
if (lean::is_scalar(x_74)) {
 x_79 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_79 = x_74;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
case 9:
{
uint8 x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_80 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_81 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_83 = x_1;
} else {
 lean::inc(x_81);
 lean::dec(x_1);
 x_83 = lean::box(0);
}
x_84 = lean::apply_1(x_0, x_81);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(9, 1, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_80);
x_86 = x_85;
return x_86;
}
case 10:
{
obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_89 = x_1;
} else {
 lean::inc(x_87);
 lean::dec(x_1);
 x_89 = lean::box(0);
}
x_90 = lean::apply_1(x_0, x_87);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 11:
{
lean::dec(x_0);
return x_1;
}
case 12:
{
obj* x_93; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_95 = x_1;
} else {
 lean::inc(x_93);
 lean::dec(x_1);
 x_95 = lean::box(0);
}
x_96 = lean::apply_1(x_0, x_93);
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(12, 1, 0);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
default:
{
obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
x_98 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_100 = x_1;
} else {
 lean::inc(x_98);
 lean::dec(x_1);
 x_100 = lean::box(0);
}
x_101 = lean::apply_1(x_0, x_98);
if (lean::is_scalar(x_100)) {
 x_102 = lean::alloc_cnstr(13, 1, 0);
} else {
 x_102 = x_100;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
}
obj* l_Lean_IR_MapVars_mapExpr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_MapVars_mapExpr___main(x_0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_1, x_11);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_17 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
lean::inc(x_0);
x_19 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_15);
if (lean::is_scalar(x_17)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_17;
}
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::array_fset(x_10, x_1, x_20);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_21;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_26 = x_8;
} else {
 lean::inc(x_24);
 lean::dec(x_8);
 x_26 = lean::box(0);
}
lean::inc(x_0);
x_28 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_24);
if (lean::is_scalar(x_26)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_26;
}
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::array_fset(x_10, x_1, x_29);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_30;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_9 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
lean::inc(x_0);
x_11 = l_Lean_IR_MapVars_mapExpr___main(x_0, x_5);
x_12 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*3, x_4);
x_14 = x_13;
return x_14;
}
case 1:
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_19 = lean::cnstr_get(x_1, 2);
x_21 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 x_23 = x_1;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_1);
 x_23 = lean::box(0);
}
lean::inc(x_0);
x_25 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_19);
x_26 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_21);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_15);
lean::cnstr_set(x_27, 1, x_17);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
case 2:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; 
x_28 = lean::cnstr_get(x_1, 0);
x_30 = lean::cnstr_get(x_1, 1);
x_32 = lean::cnstr_get(x_1, 2);
x_34 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_36 = x_1;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_1);
 x_36 = lean::box(0);
}
lean::inc(x_0);
x_38 = lean::apply_1(x_0, x_28);
lean::inc(x_0);
x_40 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_34);
if (lean::obj_tag(x_32) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_43 = x_32;
} else {
 lean::inc(x_41);
 lean::dec(x_32);
 x_43 = lean::box(0);
}
x_44 = lean::apply_1(x_0, x_41);
if (lean::is_scalar(x_43)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_43;
}
lean::cnstr_set(x_45, 0, x_44);
if (lean::is_scalar(x_36)) {
 x_46 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_46 = x_36;
}
lean::cnstr_set(x_46, 0, x_38);
lean::cnstr_set(x_46, 1, x_30);
lean::cnstr_set(x_46, 2, x_45);
lean::cnstr_set(x_46, 3, x_40);
return x_46;
}
else
{
obj* x_48; 
lean::dec(x_0);
if (lean::is_scalar(x_36)) {
 x_48 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_48 = x_36;
}
lean::cnstr_set(x_48, 0, x_38);
lean::cnstr_set(x_48, 1, x_30);
lean::cnstr_set(x_48, 2, x_32);
lean::cnstr_set(x_48, 3, x_40);
return x_48;
}
}
case 3:
{
obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_49 = lean::cnstr_get(x_1, 0);
x_51 = lean::cnstr_get(x_1, 1);
x_53 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_55 = x_1;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_1);
 x_55 = lean::box(0);
}
lean::inc(x_0);
x_57 = lean::apply_1(x_0, x_49);
x_58 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_53);
if (lean::is_scalar(x_55)) {
 x_59 = lean::alloc_cnstr(3, 3, 0);
} else {
 x_59 = x_55;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_51);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
case 4:
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_60 = lean::cnstr_get(x_1, 0);
x_62 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_1, 2);
x_66 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 x_68 = x_1;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_1);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::apply_1(x_0, x_60);
lean::inc(x_0);
x_72 = lean::apply_1(x_0, x_64);
x_73 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_66);
if (lean::is_scalar(x_68)) {
 x_74 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_74 = x_68;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set(x_74, 1, x_62);
lean::cnstr_set(x_74, 2, x_72);
lean::cnstr_set(x_74, 3, x_73);
return x_74;
}
case 5:
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_75 = lean::cnstr_get(x_1, 0);
x_77 = lean::cnstr_get(x_1, 1);
x_79 = lean::cnstr_get(x_1, 2);
x_81 = lean::cnstr_get(x_1, 3);
x_83 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_84 = lean::cnstr_get(x_1, 4);
if (lean::is_exclusive(x_1)) {
 x_86 = x_1;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_84);
 lean::dec(x_1);
 x_86 = lean::box(0);
}
lean::inc(x_0);
x_88 = lean::apply_1(x_0, x_75);
lean::inc(x_0);
x_90 = lean::apply_1(x_0, x_81);
x_91 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_84);
if (lean::is_scalar(x_86)) {
 x_92 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_92 = x_86;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set(x_92, 1, x_77);
lean::cnstr_set(x_92, 2, x_79);
lean::cnstr_set(x_92, 3, x_90);
lean::cnstr_set(x_92, 4, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*5, x_83);
x_93 = x_92;
return x_93;
}
case 6:
{
obj* x_94; obj* x_96; uint8 x_98; obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_94 = lean::cnstr_get(x_1, 0);
x_96 = lean::cnstr_get(x_1, 1);
x_98 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_99 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_101 = x_1;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::inc(x_99);
 lean::dec(x_1);
 x_101 = lean::box(0);
}
lean::inc(x_0);
x_103 = lean::apply_1(x_0, x_94);
x_104 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_99);
if (lean::is_scalar(x_101)) {
 x_105 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_105 = x_101;
}
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_96);
lean::cnstr_set(x_105, 2, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*3, x_98);
x_106 = x_105;
return x_106;
}
case 7:
{
obj* x_107; obj* x_109; uint8 x_111; obj* x_112; obj* x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_107 = lean::cnstr_get(x_1, 0);
x_109 = lean::cnstr_get(x_1, 1);
x_111 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_112 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_114 = x_1;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_112);
 lean::dec(x_1);
 x_114 = lean::box(0);
}
lean::inc(x_0);
x_116 = lean::apply_1(x_0, x_107);
x_117 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_112);
if (lean::is_scalar(x_114)) {
 x_118 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_118 = x_114;
}
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_109);
lean::cnstr_set(x_118, 2, x_117);
lean::cnstr_set_scalar(x_118, sizeof(void*)*3, x_111);
x_119 = x_118;
return x_119;
}
case 8:
{
obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
x_120 = lean::cnstr_get(x_1, 0);
x_122 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_124 = x_1;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::dec(x_1);
 x_124 = lean::box(0);
}
lean::inc(x_0);
x_126 = lean::apply_1(x_0, x_120);
x_127 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_122);
if (lean::is_scalar(x_124)) {
 x_128 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_128 = x_124;
}
lean::cnstr_set(x_128, 0, x_126);
lean::cnstr_set(x_128, 1, x_127);
return x_128;
}
case 9:
{
obj* x_129; obj* x_131; obj* x_133; obj* x_134; obj* x_135; 
x_129 = lean::cnstr_get(x_1, 0);
x_131 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_133 = x_1;
} else {
 lean::inc(x_129);
 lean::inc(x_131);
 lean::dec(x_1);
 x_133 = lean::box(0);
}
x_134 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_131);
if (lean::is_scalar(x_133)) {
 x_135 = lean::alloc_cnstr(9, 2, 0);
} else {
 x_135 = x_133;
}
lean::cnstr_set(x_135, 0, x_129);
lean::cnstr_set(x_135, 1, x_134);
return x_135;
}
case 10:
{
obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_136 = lean::cnstr_get(x_1, 0);
x_138 = lean::cnstr_get(x_1, 1);
x_140 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_142 = x_1;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::inc(x_140);
 lean::dec(x_1);
 x_142 = lean::box(0);
}
lean::inc(x_0);
x_144 = lean::apply_1(x_0, x_138);
x_145 = lean::mk_nat_obj(0ul);
x_146 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(x_0, x_145, x_140);
if (lean::is_scalar(x_142)) {
 x_147 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_147 = x_142;
}
lean::cnstr_set(x_147, 0, x_136);
lean::cnstr_set(x_147, 1, x_144);
lean::cnstr_set(x_147, 2, x_146);
return x_147;
}
case 11:
{
obj* x_148; obj* x_150; 
x_148 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_150 = x_1;
} else {
 lean::inc(x_148);
 lean::dec(x_1);
 x_150 = lean::box(0);
}
if (lean::obj_tag(x_148) == 0)
{
obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_151 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_153 = x_148;
} else {
 lean::inc(x_151);
 lean::dec(x_148);
 x_153 = lean::box(0);
}
x_154 = lean::apply_1(x_0, x_151);
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_154);
if (lean::is_scalar(x_150)) {
 x_156 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_156 = x_150;
}
lean::cnstr_set(x_156, 0, x_155);
return x_156;
}
else
{
obj* x_158; 
lean::dec(x_0);
if (lean::is_scalar(x_150)) {
 x_158 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_158 = x_150;
}
lean::cnstr_set(x_158, 0, x_148);
return x_158;
}
}
case 12:
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_159 = lean::cnstr_get(x_1, 0);
x_161 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_163 = x_1;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_1);
 x_163 = lean::box(0);
}
x_164 = lean::mk_nat_obj(0ul);
x_165 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_0, x_164, x_161);
if (lean::is_scalar(x_163)) {
 x_166 = lean::alloc_cnstr(12, 2, 0);
} else {
 x_166 = x_163;
}
lean::cnstr_set(x_166, 0, x_159);
lean::cnstr_set(x_166, 1, x_165);
return x_166;
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_Lean_IR_MapVars_mapFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_mapVars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_MapVars_mapFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_0, x_1, x_8, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_11 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_15 = x_2;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::nat_dec_eq(x_0, x_13);
if (x_16 == 0)
{
obj* x_18; 
lean::dec(x_1);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_13);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_1);
return x_20;
}
}
case 2:
{
obj* x_21; obj* x_23; uint8 x_25; obj* x_26; obj* x_28; uint8 x_29; obj* x_30; obj* x_32; 
x_21 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get(x_2, 1);
x_25 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_26 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_28 = x_2;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::inc(x_26);
 lean::dec(x_2);
 x_28 = lean::box(0);
}
x_29 = lean::nat_dec_eq(x_0, x_21);
x_30 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_32 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_0, x_1, x_30, x_26);
if (x_29 == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_1);
if (lean::is_scalar(x_28)) {
 x_34 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_34 = x_28;
}
lean::cnstr_set(x_34, 0, x_21);
lean::cnstr_set(x_34, 1, x_23);
lean::cnstr_set(x_34, 2, x_32);
lean::cnstr_set_scalar(x_34, sizeof(void*)*3, x_25);
x_35 = x_34;
return x_35;
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_21);
if (lean::is_scalar(x_28)) {
 x_37 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_37 = x_28;
}
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_23);
lean::cnstr_set(x_37, 2, x_32);
lean::cnstr_set_scalar(x_37, sizeof(void*)*3, x_25);
x_38 = x_37;
return x_38;
}
}
case 3:
{
obj* x_39; obj* x_41; obj* x_43; uint8 x_44; 
x_39 = lean::cnstr_get(x_2, 0);
x_41 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_43 = x_2;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_2);
 x_43 = lean::box(0);
}
x_44 = lean::nat_dec_eq(x_0, x_41);
if (x_44 == 0)
{
obj* x_46; 
lean::dec(x_1);
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_46 = x_43;
}
lean::cnstr_set(x_46, 0, x_39);
lean::cnstr_set(x_46, 1, x_41);
return x_46;
}
else
{
obj* x_48; 
lean::dec(x_41);
if (lean::is_scalar(x_43)) {
 x_48 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_48 = x_43;
}
lean::cnstr_set(x_48, 0, x_39);
lean::cnstr_set(x_48, 1, x_1);
return x_48;
}
}
case 4:
{
obj* x_49; obj* x_51; obj* x_53; uint8 x_54; 
x_49 = lean::cnstr_get(x_2, 0);
x_51 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_53 = x_2;
} else {
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_2);
 x_53 = lean::box(0);
}
x_54 = lean::nat_dec_eq(x_0, x_51);
if (x_54 == 0)
{
obj* x_56; 
lean::dec(x_1);
if (lean::is_scalar(x_53)) {
 x_56 = lean::alloc_cnstr(4, 2, 0);
} else {
 x_56 = x_53;
}
lean::cnstr_set(x_56, 0, x_49);
lean::cnstr_set(x_56, 1, x_51);
return x_56;
}
else
{
obj* x_58; 
lean::dec(x_51);
if (lean::is_scalar(x_53)) {
 x_58 = lean::alloc_cnstr(4, 2, 0);
} else {
 x_58 = x_53;
}
lean::cnstr_set(x_58, 0, x_49);
lean::cnstr_set(x_58, 1, x_1);
return x_58;
}
}
case 5:
{
obj* x_59; obj* x_61; obj* x_63; obj* x_65; uint8 x_66; 
x_59 = lean::cnstr_get(x_2, 0);
x_61 = lean::cnstr_get(x_2, 1);
x_63 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_65 = x_2;
} else {
 lean::inc(x_59);
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_2);
 x_65 = lean::box(0);
}
x_66 = lean::nat_dec_eq(x_0, x_63);
if (x_66 == 0)
{
obj* x_68; 
lean::dec(x_1);
if (lean::is_scalar(x_65)) {
 x_68 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_68 = x_65;
}
lean::cnstr_set(x_68, 0, x_59);
lean::cnstr_set(x_68, 1, x_61);
lean::cnstr_set(x_68, 2, x_63);
return x_68;
}
else
{
obj* x_70; 
lean::dec(x_63);
if (lean::is_scalar(x_65)) {
 x_70 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_70 = x_65;
}
lean::cnstr_set(x_70, 0, x_59);
lean::cnstr_set(x_70, 1, x_61);
lean::cnstr_set(x_70, 2, x_1);
return x_70;
}
}
case 6:
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = lean::cnstr_get(x_2, 0);
x_73 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_75 = x_2;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_2);
 x_75 = lean::box(0);
}
x_76 = lean::mk_nat_obj(0ul);
x_77 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_0, x_1, x_76, x_73);
if (lean::is_scalar(x_75)) {
 x_78 = lean::alloc_cnstr(6, 2, 0);
} else {
 x_78 = x_75;
}
lean::cnstr_set(x_78, 0, x_71);
lean::cnstr_set(x_78, 1, x_77);
return x_78;
}
case 7:
{
obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_79 = lean::cnstr_get(x_2, 0);
x_81 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_83 = x_2;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_2);
 x_83 = lean::box(0);
}
x_84 = lean::mk_nat_obj(0ul);
x_85 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_0, x_1, x_84, x_81);
if (lean::is_scalar(x_83)) {
 x_86 = lean::alloc_cnstr(7, 2, 0);
} else {
 x_86 = x_83;
}
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
case 8:
{
obj* x_87; obj* x_89; obj* x_91; uint8 x_92; obj* x_93; obj* x_95; 
x_87 = lean::cnstr_get(x_2, 0);
x_89 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_91 = x_2;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_2);
 x_91 = lean::box(0);
}
x_92 = lean::nat_dec_eq(x_0, x_87);
x_93 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_95 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_0, x_1, x_93, x_89);
if (x_92 == 0)
{
obj* x_97; 
lean::dec(x_1);
if (lean::is_scalar(x_91)) {
 x_97 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_97 = x_91;
}
lean::cnstr_set(x_97, 0, x_87);
lean::cnstr_set(x_97, 1, x_95);
return x_97;
}
else
{
obj* x_99; 
lean::dec(x_87);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_95);
return x_99;
}
}
case 9:
{
uint8 x_100; obj* x_101; obj* x_103; uint8 x_104; 
x_100 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_101 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_103 = x_2;
} else {
 lean::inc(x_101);
 lean::dec(x_2);
 x_103 = lean::box(0);
}
x_104 = lean::nat_dec_eq(x_0, x_101);
if (x_104 == 0)
{
obj* x_106; obj* x_107; 
lean::dec(x_1);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(9, 1, 1);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_101);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_100);
x_107 = x_106;
return x_107;
}
else
{
obj* x_109; obj* x_110; 
lean::dec(x_101);
if (lean::is_scalar(x_103)) {
 x_109 = lean::alloc_cnstr(9, 1, 1);
} else {
 x_109 = x_103;
}
lean::cnstr_set(x_109, 0, x_1);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_100);
x_110 = x_109;
return x_110;
}
}
case 10:
{
obj* x_111; obj* x_113; uint8 x_114; 
x_111 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_113 = x_2;
} else {
 lean::inc(x_111);
 lean::dec(x_2);
 x_113 = lean::box(0);
}
x_114 = lean::nat_dec_eq(x_0, x_111);
if (x_114 == 0)
{
obj* x_116; 
lean::dec(x_1);
if (lean::is_scalar(x_113)) {
 x_116 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_116 = x_113;
}
lean::cnstr_set(x_116, 0, x_111);
return x_116;
}
else
{
obj* x_118; 
lean::dec(x_111);
if (lean::is_scalar(x_113)) {
 x_118 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_118 = x_113;
}
lean::cnstr_set(x_118, 0, x_1);
return x_118;
}
}
case 11:
{
lean::dec(x_1);
return x_2;
}
case 12:
{
obj* x_120; obj* x_122; uint8 x_123; 
x_120 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_122 = x_2;
} else {
 lean::inc(x_120);
 lean::dec(x_2);
 x_122 = lean::box(0);
}
x_123 = lean::nat_dec_eq(x_0, x_120);
if (x_123 == 0)
{
obj* x_125; 
lean::dec(x_1);
if (lean::is_scalar(x_122)) {
 x_125 = lean::alloc_cnstr(12, 1, 0);
} else {
 x_125 = x_122;
}
lean::cnstr_set(x_125, 0, x_120);
return x_125;
}
else
{
obj* x_127; 
lean::dec(x_120);
if (lean::is_scalar(x_122)) {
 x_127 = lean::alloc_cnstr(12, 1, 0);
} else {
 x_127 = x_122;
}
lean::cnstr_set(x_127, 0, x_1);
return x_127;
}
}
default:
{
obj* x_128; obj* x_130; uint8 x_131; 
x_128 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_130 = x_2;
} else {
 lean::inc(x_128);
 lean::dec(x_2);
 x_130 = lean::box(0);
}
x_131 = lean::nat_dec_eq(x_0, x_128);
if (x_131 == 0)
{
obj* x_133; 
lean::dec(x_1);
if (lean::is_scalar(x_130)) {
 x_133 = lean::alloc_cnstr(13, 1, 0);
} else {
 x_133 = x_130;
}
lean::cnstr_set(x_133, 0, x_128);
return x_133;
}
else
{
obj* x_135; 
lean::dec(x_128);
if (lean::is_scalar(x_130)) {
 x_135 = lean::alloc_cnstr(13, 1, 0);
} else {
 x_135 = x_130;
}
lean::cnstr_set(x_135, 0, x_1);
return x_135;
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
lean::inc(x_1);
x_20 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_16);
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::array_fset(x_11, x_2, x_21);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_22;
goto _start;
}
else
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_27 = x_9;
} else {
 lean::inc(x_25);
 lean::dec(x_9);
 x_27 = lean::box(0);
}
lean::inc(x_1);
x_29 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_25);
if (lean::is_scalar(x_27)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_27;
}
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::array_fset(x_11, x_2, x_30);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_31;
goto _start;
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(1);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; uint8 x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::nat_dec_eq(x_0, x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_14);
x_19 = lean::array_fset(x_11, x_2, x_18);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::inc(x_1);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::array_fset(x_11, x_2, x_24);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
else
{
obj* x_28; 
x_28 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_2, 1);
x_8 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
lean::inc(x_1);
x_12 = l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(x_0, x_1, x_6);
x_13 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*3, x_5);
x_15 = x_14;
return x_15;
}
case 1:
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_2, 0);
x_18 = lean::cnstr_get(x_2, 1);
x_20 = lean::cnstr_get(x_2, 2);
x_22 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 x_24 = x_2;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_2);
 x_24 = lean::box(0);
}
lean::inc(x_1);
x_26 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_20);
x_27 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_22);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_16);
lean::cnstr_set(x_28, 1, x_18);
lean::cnstr_set(x_28, 2, x_26);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
case 2:
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; obj* x_40; 
x_29 = lean::cnstr_get(x_2, 0);
x_31 = lean::cnstr_get(x_2, 1);
x_33 = lean::cnstr_get(x_2, 2);
x_35 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_37 = x_2;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_2);
 x_37 = lean::box(0);
}
x_38 = lean::nat_dec_eq(x_0, x_29);
lean::inc(x_1);
x_40 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_35);
if (x_38 == 0)
{
if (lean::obj_tag(x_33) == 0)
{
obj* x_41; obj* x_43; uint8 x_44; 
x_41 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_43 = x_33;
} else {
 lean::inc(x_41);
 lean::dec(x_33);
 x_43 = lean::box(0);
}
x_44 = lean::nat_dec_eq(x_0, x_41);
if (x_44 == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_1);
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_43;
}
lean::cnstr_set(x_46, 0, x_41);
if (lean::is_scalar(x_37)) {
 x_47 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_47 = x_37;
}
lean::cnstr_set(x_47, 0, x_29);
lean::cnstr_set(x_47, 1, x_31);
lean::cnstr_set(x_47, 2, x_46);
lean::cnstr_set(x_47, 3, x_40);
return x_47;
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_41);
if (lean::is_scalar(x_43)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_43;
}
lean::cnstr_set(x_49, 0, x_1);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_50 = x_37;
}
lean::cnstr_set(x_50, 0, x_29);
lean::cnstr_set(x_50, 1, x_31);
lean::cnstr_set(x_50, 2, x_49);
lean::cnstr_set(x_50, 3, x_40);
return x_50;
}
}
else
{
obj* x_52; 
lean::dec(x_1);
if (lean::is_scalar(x_37)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_37;
}
lean::cnstr_set(x_52, 0, x_29);
lean::cnstr_set(x_52, 1, x_31);
lean::cnstr_set(x_52, 2, x_33);
lean::cnstr_set(x_52, 3, x_40);
return x_52;
}
}
else
{
lean::dec(x_29);
if (lean::obj_tag(x_33) == 0)
{
obj* x_54; obj* x_56; uint8 x_57; 
x_54 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_set(x_33, 0, lean::box(0));
 x_56 = x_33;
} else {
 lean::inc(x_54);
 lean::dec(x_33);
 x_56 = lean::box(0);
}
x_57 = lean::nat_dec_eq(x_0, x_54);
if (x_57 == 0)
{
obj* x_58; obj* x_59; 
if (lean::is_scalar(x_56)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_56;
}
lean::cnstr_set(x_58, 0, x_54);
if (lean::is_scalar(x_37)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_37;
}
lean::cnstr_set(x_59, 0, x_1);
lean::cnstr_set(x_59, 1, x_31);
lean::cnstr_set(x_59, 2, x_58);
lean::cnstr_set(x_59, 3, x_40);
return x_59;
}
else
{
obj* x_62; obj* x_63; 
lean::dec(x_54);
lean::inc(x_1);
if (lean::is_scalar(x_56)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_56;
}
lean::cnstr_set(x_62, 0, x_1);
if (lean::is_scalar(x_37)) {
 x_63 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_63 = x_37;
}
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_31);
lean::cnstr_set(x_63, 2, x_62);
lean::cnstr_set(x_63, 3, x_40);
return x_63;
}
}
else
{
obj* x_64; 
if (lean::is_scalar(x_37)) {
 x_64 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_64 = x_37;
}
lean::cnstr_set(x_64, 0, x_1);
lean::cnstr_set(x_64, 1, x_31);
lean::cnstr_set(x_64, 2, x_33);
lean::cnstr_set(x_64, 3, x_40);
return x_64;
}
}
}
case 3:
{
obj* x_65; obj* x_67; obj* x_69; obj* x_71; uint8 x_72; obj* x_74; 
x_65 = lean::cnstr_get(x_2, 0);
x_67 = lean::cnstr_get(x_2, 1);
x_69 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_71 = x_2;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::dec(x_2);
 x_71 = lean::box(0);
}
x_72 = lean::nat_dec_eq(x_0, x_65);
lean::inc(x_1);
x_74 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_69);
if (x_72 == 0)
{
obj* x_76; 
lean::dec(x_1);
if (lean::is_scalar(x_71)) {
 x_76 = lean::alloc_cnstr(3, 3, 0);
} else {
 x_76 = x_71;
}
lean::cnstr_set(x_76, 0, x_65);
lean::cnstr_set(x_76, 1, x_67);
lean::cnstr_set(x_76, 2, x_74);
return x_76;
}
else
{
obj* x_78; 
lean::dec(x_65);
if (lean::is_scalar(x_71)) {
 x_78 = lean::alloc_cnstr(3, 3, 0);
} else {
 x_78 = x_71;
}
lean::cnstr_set(x_78, 0, x_1);
lean::cnstr_set(x_78, 1, x_67);
lean::cnstr_set(x_78, 2, x_74);
return x_78;
}
}
case 4:
{
obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_87; uint8 x_88; uint8 x_89; obj* x_91; 
x_79 = lean::cnstr_get(x_2, 0);
x_81 = lean::cnstr_get(x_2, 1);
x_83 = lean::cnstr_get(x_2, 2);
x_85 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_87 = x_2;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_2);
 x_87 = lean::box(0);
}
x_88 = lean::nat_dec_eq(x_0, x_79);
x_89 = lean::nat_dec_eq(x_0, x_83);
lean::inc(x_1);
x_91 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_85);
if (x_88 == 0)
{
if (x_89 == 0)
{
obj* x_93; 
lean::dec(x_1);
if (lean::is_scalar(x_87)) {
 x_93 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_93 = x_87;
}
lean::cnstr_set(x_93, 0, x_79);
lean::cnstr_set(x_93, 1, x_81);
lean::cnstr_set(x_93, 2, x_83);
lean::cnstr_set(x_93, 3, x_91);
return x_93;
}
else
{
obj* x_95; 
lean::dec(x_83);
if (lean::is_scalar(x_87)) {
 x_95 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_95 = x_87;
}
lean::cnstr_set(x_95, 0, x_79);
lean::cnstr_set(x_95, 1, x_81);
lean::cnstr_set(x_95, 2, x_1);
lean::cnstr_set(x_95, 3, x_91);
return x_95;
}
}
else
{
lean::dec(x_79);
if (x_89 == 0)
{
obj* x_97; 
if (lean::is_scalar(x_87)) {
 x_97 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_97 = x_87;
}
lean::cnstr_set(x_97, 0, x_1);
lean::cnstr_set(x_97, 1, x_81);
lean::cnstr_set(x_97, 2, x_83);
lean::cnstr_set(x_97, 3, x_91);
return x_97;
}
else
{
obj* x_100; 
lean::dec(x_83);
lean::inc(x_1);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(4, 4, 0);
} else {
 x_100 = x_87;
}
lean::cnstr_set(x_100, 0, x_1);
lean::cnstr_set(x_100, 1, x_81);
lean::cnstr_set(x_100, 2, x_1);
lean::cnstr_set(x_100, 3, x_91);
return x_100;
}
}
}
case 5:
{
obj* x_101; obj* x_103; obj* x_105; obj* x_107; uint8 x_109; obj* x_110; obj* x_112; uint8 x_113; uint8 x_114; obj* x_116; 
x_101 = lean::cnstr_get(x_2, 0);
x_103 = lean::cnstr_get(x_2, 1);
x_105 = lean::cnstr_get(x_2, 2);
x_107 = lean::cnstr_get(x_2, 3);
x_109 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_110 = lean::cnstr_get(x_2, 4);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 lean::cnstr_set(x_2, 4, lean::box(0));
 x_112 = x_2;
} else {
 lean::inc(x_101);
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::inc(x_110);
 lean::dec(x_2);
 x_112 = lean::box(0);
}
x_113 = lean::nat_dec_eq(x_0, x_101);
x_114 = lean::nat_dec_eq(x_0, x_107);
lean::inc(x_1);
x_116 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_110);
if (x_113 == 0)
{
if (x_114 == 0)
{
obj* x_118; obj* x_119; 
lean::dec(x_1);
if (lean::is_scalar(x_112)) {
 x_118 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_118 = x_112;
}
lean::cnstr_set(x_118, 0, x_101);
lean::cnstr_set(x_118, 1, x_103);
lean::cnstr_set(x_118, 2, x_105);
lean::cnstr_set(x_118, 3, x_107);
lean::cnstr_set(x_118, 4, x_116);
lean::cnstr_set_scalar(x_118, sizeof(void*)*5, x_109);
x_119 = x_118;
return x_119;
}
else
{
obj* x_121; obj* x_122; 
lean::dec(x_107);
if (lean::is_scalar(x_112)) {
 x_121 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_121 = x_112;
}
lean::cnstr_set(x_121, 0, x_101);
lean::cnstr_set(x_121, 1, x_103);
lean::cnstr_set(x_121, 2, x_105);
lean::cnstr_set(x_121, 3, x_1);
lean::cnstr_set(x_121, 4, x_116);
lean::cnstr_set_scalar(x_121, sizeof(void*)*5, x_109);
x_122 = x_121;
return x_122;
}
}
else
{
lean::dec(x_101);
if (x_114 == 0)
{
obj* x_124; obj* x_125; 
if (lean::is_scalar(x_112)) {
 x_124 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_124 = x_112;
}
lean::cnstr_set(x_124, 0, x_1);
lean::cnstr_set(x_124, 1, x_103);
lean::cnstr_set(x_124, 2, x_105);
lean::cnstr_set(x_124, 3, x_107);
lean::cnstr_set(x_124, 4, x_116);
lean::cnstr_set_scalar(x_124, sizeof(void*)*5, x_109);
x_125 = x_124;
return x_125;
}
else
{
obj* x_128; obj* x_129; 
lean::dec(x_107);
lean::inc(x_1);
if (lean::is_scalar(x_112)) {
 x_128 = lean::alloc_cnstr(5, 5, 1);
} else {
 x_128 = x_112;
}
lean::cnstr_set(x_128, 0, x_1);
lean::cnstr_set(x_128, 1, x_103);
lean::cnstr_set(x_128, 2, x_105);
lean::cnstr_set(x_128, 3, x_1);
lean::cnstr_set(x_128, 4, x_116);
lean::cnstr_set_scalar(x_128, sizeof(void*)*5, x_109);
x_129 = x_128;
return x_129;
}
}
}
case 6:
{
obj* x_130; obj* x_132; uint8 x_134; obj* x_135; obj* x_137; uint8 x_138; obj* x_140; 
x_130 = lean::cnstr_get(x_2, 0);
x_132 = lean::cnstr_get(x_2, 1);
x_134 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_135 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_137 = x_2;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::inc(x_135);
 lean::dec(x_2);
 x_137 = lean::box(0);
}
x_138 = lean::nat_dec_eq(x_0, x_130);
lean::inc(x_1);
x_140 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_135);
if (x_138 == 0)
{
obj* x_142; obj* x_143; 
lean::dec(x_1);
if (lean::is_scalar(x_137)) {
 x_142 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_142 = x_137;
}
lean::cnstr_set(x_142, 0, x_130);
lean::cnstr_set(x_142, 1, x_132);
lean::cnstr_set(x_142, 2, x_140);
lean::cnstr_set_scalar(x_142, sizeof(void*)*3, x_134);
x_143 = x_142;
return x_143;
}
else
{
obj* x_145; obj* x_146; 
lean::dec(x_130);
if (lean::is_scalar(x_137)) {
 x_145 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_145 = x_137;
}
lean::cnstr_set(x_145, 0, x_1);
lean::cnstr_set(x_145, 1, x_132);
lean::cnstr_set(x_145, 2, x_140);
lean::cnstr_set_scalar(x_145, sizeof(void*)*3, x_134);
x_146 = x_145;
return x_146;
}
}
case 7:
{
obj* x_147; obj* x_149; uint8 x_151; obj* x_152; obj* x_154; uint8 x_155; obj* x_157; 
x_147 = lean::cnstr_get(x_2, 0);
x_149 = lean::cnstr_get(x_2, 1);
x_151 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_152 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_154 = x_2;
} else {
 lean::inc(x_147);
 lean::inc(x_149);
 lean::inc(x_152);
 lean::dec(x_2);
 x_154 = lean::box(0);
}
x_155 = lean::nat_dec_eq(x_0, x_147);
lean::inc(x_1);
x_157 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_152);
if (x_155 == 0)
{
obj* x_159; obj* x_160; 
lean::dec(x_1);
if (lean::is_scalar(x_154)) {
 x_159 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_159 = x_154;
}
lean::cnstr_set(x_159, 0, x_147);
lean::cnstr_set(x_159, 1, x_149);
lean::cnstr_set(x_159, 2, x_157);
lean::cnstr_set_scalar(x_159, sizeof(void*)*3, x_151);
x_160 = x_159;
return x_160;
}
else
{
obj* x_162; obj* x_163; 
lean::dec(x_147);
if (lean::is_scalar(x_154)) {
 x_162 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_162 = x_154;
}
lean::cnstr_set(x_162, 0, x_1);
lean::cnstr_set(x_162, 1, x_149);
lean::cnstr_set(x_162, 2, x_157);
lean::cnstr_set_scalar(x_162, sizeof(void*)*3, x_151);
x_163 = x_162;
return x_163;
}
}
case 8:
{
obj* x_164; obj* x_166; obj* x_168; uint8 x_169; obj* x_171; 
x_164 = lean::cnstr_get(x_2, 0);
x_166 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_168 = x_2;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::dec(x_2);
 x_168 = lean::box(0);
}
x_169 = lean::nat_dec_eq(x_0, x_164);
lean::inc(x_1);
x_171 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_166);
if (x_169 == 0)
{
obj* x_173; 
lean::dec(x_1);
if (lean::is_scalar(x_168)) {
 x_173 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_173 = x_168;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_171);
return x_173;
}
else
{
obj* x_175; 
lean::dec(x_164);
if (lean::is_scalar(x_168)) {
 x_175 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_175 = x_168;
}
lean::cnstr_set(x_175, 0, x_1);
lean::cnstr_set(x_175, 1, x_171);
return x_175;
}
}
case 9:
{
obj* x_176; obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
x_176 = lean::cnstr_get(x_2, 0);
x_178 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_180 = x_2;
} else {
 lean::inc(x_176);
 lean::inc(x_178);
 lean::dec(x_2);
 x_180 = lean::box(0);
}
x_181 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_178);
if (lean::is_scalar(x_180)) {
 x_182 = lean::alloc_cnstr(9, 2, 0);
} else {
 x_182 = x_180;
}
lean::cnstr_set(x_182, 0, x_176);
lean::cnstr_set(x_182, 1, x_181);
return x_182;
}
case 10:
{
obj* x_183; obj* x_185; obj* x_187; obj* x_189; uint8 x_190; obj* x_191; obj* x_193; 
x_183 = lean::cnstr_get(x_2, 0);
x_185 = lean::cnstr_get(x_2, 1);
x_187 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_189 = x_2;
} else {
 lean::inc(x_183);
 lean::inc(x_185);
 lean::inc(x_187);
 lean::dec(x_2);
 x_189 = lean::box(0);
}
x_190 = lean::nat_dec_eq(x_0, x_185);
x_191 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_193 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_0, x_1, x_191, x_187);
if (x_190 == 0)
{
obj* x_195; 
lean::dec(x_1);
if (lean::is_scalar(x_189)) {
 x_195 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_195 = x_189;
}
lean::cnstr_set(x_195, 0, x_183);
lean::cnstr_set(x_195, 1, x_185);
lean::cnstr_set(x_195, 2, x_193);
return x_195;
}
else
{
obj* x_197; 
lean::dec(x_185);
if (lean::is_scalar(x_189)) {
 x_197 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_197 = x_189;
}
lean::cnstr_set(x_197, 0, x_183);
lean::cnstr_set(x_197, 1, x_1);
lean::cnstr_set(x_197, 2, x_193);
return x_197;
}
}
case 11:
{
obj* x_198; obj* x_200; 
x_198 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_200 = x_2;
} else {
 lean::inc(x_198);
 lean::dec(x_2);
 x_200 = lean::box(0);
}
if (lean::obj_tag(x_198) == 0)
{
obj* x_201; obj* x_203; uint8 x_204; 
x_201 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 lean::cnstr_set(x_198, 0, lean::box(0));
 x_203 = x_198;
} else {
 lean::inc(x_201);
 lean::dec(x_198);
 x_203 = lean::box(0);
}
x_204 = lean::nat_dec_eq(x_0, x_201);
if (x_204 == 0)
{
obj* x_206; obj* x_207; 
lean::dec(x_1);
if (lean::is_scalar(x_203)) {
 x_206 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_206 = x_203;
}
lean::cnstr_set(x_206, 0, x_201);
if (lean::is_scalar(x_200)) {
 x_207 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_207 = x_200;
}
lean::cnstr_set(x_207, 0, x_206);
return x_207;
}
else
{
obj* x_209; obj* x_210; 
lean::dec(x_201);
if (lean::is_scalar(x_203)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_203;
}
lean::cnstr_set(x_209, 0, x_1);
if (lean::is_scalar(x_200)) {
 x_210 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_210 = x_200;
}
lean::cnstr_set(x_210, 0, x_209);
return x_210;
}
}
else
{
obj* x_212; 
lean::dec(x_1);
if (lean::is_scalar(x_200)) {
 x_212 = lean::alloc_cnstr(11, 1, 0);
} else {
 x_212 = x_200;
}
lean::cnstr_set(x_212, 0, x_198);
return x_212;
}
}
case 12:
{
obj* x_213; obj* x_215; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
x_213 = lean::cnstr_get(x_2, 0);
x_215 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_217 = x_2;
} else {
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_2);
 x_217 = lean::box(0);
}
x_218 = lean::mk_nat_obj(0ul);
x_219 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_0, x_1, x_218, x_215);
if (lean::is_scalar(x_217)) {
 x_220 = lean::alloc_cnstr(12, 2, 0);
} else {
 x_220 = x_217;
}
lean::cnstr_set(x_220, 0, x_213);
lean::cnstr_set(x_220, 1, x_219);
return x_220;
}
default:
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Lean_IR_FnBody_replaceVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_FnBody_replaceVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_FnBody_replaceVar(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* initialize_init_control_reader(obj*);
obj* initialize_init_control_conditional(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_normids(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1);
 l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1);
return w;
}
