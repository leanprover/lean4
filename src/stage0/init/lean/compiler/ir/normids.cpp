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
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkParams(obj*, obj*);
obj* l_Lean_IR_FnBody_replaceVar(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr___main___boxed(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_uniqueIds(obj*);
obj* l_Lean_IR_NormalizeIds_normArgs___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_UniqueIds_checkFnBody(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normDecl___main(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normVar(obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg___boxed(obj*, obj*);
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
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_NormalizeIds_normJP___boxed(obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
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
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg___main___boxed(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_MtoN___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normIndex(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l_Lean_IR_MapVars_mapFnBody(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr___boxed(obj*, obj*);
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
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_MapVars_mapExpr___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withVar(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(obj* x_1, obj* x_2) {
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
x_8 = lean::nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = lean::nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_6);
lean::inc(x_5);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_6);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_13; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = lean::nat_dec_lt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = lean::nat_dec_lt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = lean::nat_dec_lt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = lean::nat_dec_lt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = lean::nat_dec_lt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = lean::nat_dec_lt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
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
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
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
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = lean::nat_dec_lt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = lean::nat_dec_lt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
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
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
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
}
obj* l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_IR_UniqueIds_checkId___spec__3(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_Lean_IR_UniqueIds_checkId(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(x_2, x_1, x_4);
x_6 = 1;
x_7 = lean::box(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8 x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_1);
x_9 = 0;
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
}
}
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_6 = 0;
x_7 = lean::box(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = l_Lean_IR_UniqueIds_checkId(x_10, x_3);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
uint8 x_14; 
lean::dec(x_2);
x_14 = !lean::is_exclusive(x_11);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::dec(x_15);
x_16 = 1;
x_17 = lean::box(x_16);
lean::cnstr_set(x_11, 0, x_17);
return x_11;
}
else
{
obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
lean::dec(x_11);
x_19 = 1;
x_20 = lean::box(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_2, x_23);
lean::dec(x_2);
x_2 = x_24;
x_3 = x_22;
goto _start;
}
}
}
}
obj* l_Lean_IR_UniqueIds_checkParams(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_3, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::unbox(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = 1;
x_10 = lean::box(x_9);
lean::cnstr_set(x_4, 0, x_10);
return x_4;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = 1;
x_13 = lean::box(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_4);
if (x_15 == 0)
{
obj* x_16; uint8 x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_4, 0);
lean::dec(x_16);
x_17 = 0;
x_18 = lean::box(x_17);
lean::cnstr_set(x_4, 0, x_18);
return x_4;
}
else
{
obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_4, 1);
lean::inc(x_19);
lean::dec(x_4);
x_20 = 0;
x_21 = lean::box(x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkParams___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_UniqueIds_checkParams___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkParams(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_6 = 0;
x_7 = lean::box(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_1, x_2);
x_10 = l_Lean_IR_AltCore_body___main(x_9);
lean::dec(x_9);
x_11 = l_Lean_IR_UniqueIds_checkFnBody___main(x_10, x_3);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
uint8 x_14; 
lean::dec(x_2);
x_14 = !lean::is_exclusive(x_11);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::dec(x_15);
x_16 = 1;
x_17 = lean::box(x_16);
lean::cnstr_set(x_11, 0, x_17);
return x_11;
}
else
{
obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
lean::dec(x_11);
x_19 = 1;
x_20 = lean::box(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_2, x_23);
lean::dec(x_2);
x_2 = x_24;
x_3 = x_22;
goto _start;
}
}
}
}
obj* l_Lean_IR_UniqueIds_checkFnBody___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
lean::dec(x_1);
x_13 = l_Lean_IR_UniqueIds_checkId(x_11, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_16; 
lean::dec(x_12);
x_16 = !lean::is_exclusive(x_13);
if (x_16 == 0)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_13, 0);
lean::dec(x_17);
return x_13;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_14);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
lean::dec(x_13);
x_1 = x_12;
x_2 = x_20;
goto _start;
}
}
case 1:
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_1, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_1, 3);
lean::inc(x_24);
lean::dec(x_1);
x_25 = l_Lean_IR_UniqueIds_checkId(x_22, x_2);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
uint8 x_28; 
lean::dec(x_24);
lean::dec(x_23);
x_28 = !lean::is_exclusive(x_25);
if (x_28 == 0)
{
obj* x_29; 
x_29 = lean::cnstr_get(x_25, 0);
lean::dec(x_29);
return x_25;
}
else
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_26);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
lean::dec(x_26);
x_32 = lean::cnstr_get(x_25, 1);
lean::inc(x_32);
lean::dec(x_25);
x_33 = l_Lean_IR_UniqueIds_checkParams(x_23, x_32);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::unbox(x_34);
if (x_35 == 0)
{
uint8 x_36; 
lean::dec(x_24);
x_36 = !lean::is_exclusive(x_33);
if (x_36 == 0)
{
obj* x_37; 
x_37 = lean::cnstr_get(x_33, 0);
lean::dec(x_37);
return x_33;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
lean::dec(x_33);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_34);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::dec(x_33);
x_1 = x_24;
x_2 = x_40;
goto _start;
}
}
}
case 10:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_42 = lean::cnstr_get(x_1, 2);
lean::inc(x_42);
lean::dec(x_1);
x_43 = lean::mk_nat_obj(0u);
x_44 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_42, x_43, x_2);
lean::dec(x_42);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::unbox(x_45);
lean::dec(x_45);
if (x_46 == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_44);
if (x_47 == 0)
{
obj* x_48; uint8 x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_44, 0);
lean::dec(x_48);
x_49 = 1;
x_50 = lean::box(x_49);
lean::cnstr_set(x_44, 0, x_50);
return x_44;
}
else
{
obj* x_51; uint8 x_52; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
lean::dec(x_44);
x_52 = 1;
x_53 = lean::box(x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_44);
if (x_55 == 0)
{
obj* x_56; uint8 x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_44, 0);
lean::dec(x_56);
x_57 = 0;
x_58 = lean::box(x_57);
lean::cnstr_set(x_44, 0, x_58);
return x_44;
}
else
{
obj* x_59; uint8 x_60; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_44, 1);
lean::inc(x_59);
lean::dec(x_44);
x_60 = 0;
x_61 = lean::box(x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_59);
return x_62;
}
}
}
default: 
{
obj* x_63; 
x_63 = lean::box(0);
x_3 = x_63;
goto block_10;
}
}
block_10:
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
uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_7 = 1;
x_8 = lean::box(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_anyMAux___main___at_Lean_IR_UniqueIds_checkFnBody___main___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_UniqueIds_checkFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_UniqueIds_checkDecl___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_IR_UniqueIds_checkParams(x_3, x_2);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::unbox(x_6);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_4);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
return x_5;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_13 = l_Lean_IR_UniqueIds_checkFnBody___main(x_4, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_15 = l_Lean_IR_UniqueIds_checkParams(x_14, x_2);
lean::dec(x_14);
return x_15;
}
}
}
obj* l_Lean_IR_UniqueIds_checkDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_UniqueIds_checkDecl___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Decl_uniqueIds(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_Lean_IR_UniqueIds_checkDecl___main(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_normIndex(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Lean_IR_NormalizeIds_normIndex___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normVar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normVar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normJP(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normIndex(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normJP___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normJP(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normArg___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = l_Lean_IR_NormalizeIds_normIndex(x_4, x_2);
lean::dec(x_4);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = l_Lean_IR_NormalizeIds_normIndex(x_6, x_2);
lean::dec(x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
return x_1;
}
}
}
obj* l_Lean_IR_NormalizeIds_normArg___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normArg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normArg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = lean::box(1);
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = l_Lean_IR_NormalizeIds_normArg___main(x_6, x_1);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_2, x_10);
x_12 = lean::array_fset(x_8, x_2, x_9);
lean::dec(x_2);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
obj* l_Lean_IR_NormalizeIds_normArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_3, x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_normArgs___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normArgs(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normExpr___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_5, x_4);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_9, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
case 1:
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 1);
x_14 = l_Lean_IR_NormalizeIds_normIndex(x_13, x_2);
lean::dec(x_13);
lean::cnstr_set(x_1, 1, x_14);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_2);
lean::dec(x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
case 2:
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_1);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 2);
x_22 = l_Lean_IR_NormalizeIds_normIndex(x_20, x_2);
lean::dec(x_20);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_23, x_21);
lean::cnstr_set(x_1, 2, x_24);
lean::cnstr_set(x_1, 0, x_22);
return x_1;
}
else
{
obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_1, 0);
x_26 = lean::cnstr_get(x_1, 1);
x_27 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_28 = lean::cnstr_get(x_1, 2);
lean::inc(x_28);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_1);
x_29 = l_Lean_IR_NormalizeIds_normIndex(x_25, x_2);
lean::dec(x_25);
x_30 = lean::mk_nat_obj(0u);
x_31 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_30, x_28);
x_32 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_32, 0, x_29);
lean::cnstr_set(x_32, 1, x_26);
lean::cnstr_set(x_32, 2, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_27);
return x_32;
}
}
case 3:
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_1);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_1, 1);
x_35 = l_Lean_IR_NormalizeIds_normIndex(x_34, x_2);
lean::dec(x_34);
lean::cnstr_set(x_1, 1, x_35);
return x_1;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_1, 0);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_1);
x_38 = l_Lean_IR_NormalizeIds_normIndex(x_37, x_2);
lean::dec(x_37);
x_39 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
case 4:
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_1);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_1, 1);
x_42 = l_Lean_IR_NormalizeIds_normIndex(x_41, x_2);
lean::dec(x_41);
lean::cnstr_set(x_1, 1, x_42);
return x_1;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_1, 0);
x_44 = lean::cnstr_get(x_1, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_1);
x_45 = l_Lean_IR_NormalizeIds_normIndex(x_44, x_2);
lean::dec(x_44);
x_46 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
case 5:
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_1);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_1, 2);
x_49 = l_Lean_IR_NormalizeIds_normIndex(x_48, x_2);
lean::dec(x_48);
lean::cnstr_set(x_1, 2, x_49);
return x_1;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_1, 0);
x_51 = lean::cnstr_get(x_1, 1);
x_52 = lean::cnstr_get(x_1, 2);
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_1);
x_53 = l_Lean_IR_NormalizeIds_normIndex(x_52, x_2);
lean::dec(x_52);
x_54 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
}
case 6:
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_1);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_1, 1);
x_57 = lean::mk_nat_obj(0u);
x_58 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_57, x_56);
lean::cnstr_set(x_1, 1, x_58);
return x_1;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_1, 0);
x_60 = lean::cnstr_get(x_1, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_1);
x_61 = lean::mk_nat_obj(0u);
x_62 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_61, x_60);
x_63 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
case 7:
{
uint8 x_64; 
x_64 = !lean::is_exclusive(x_1);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_1, 1);
x_66 = lean::mk_nat_obj(0u);
x_67 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_66, x_65);
lean::cnstr_set(x_1, 1, x_67);
return x_1;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_1, 0);
x_69 = lean::cnstr_get(x_1, 1);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_1);
x_70 = lean::mk_nat_obj(0u);
x_71 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_70, x_69);
x_72 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
}
case 8:
{
uint8 x_73; 
x_73 = !lean::is_exclusive(x_1);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_74 = lean::cnstr_get(x_1, 0);
x_75 = lean::cnstr_get(x_1, 1);
x_76 = l_Lean_IR_NormalizeIds_normIndex(x_74, x_2);
lean::dec(x_74);
x_77 = lean::mk_nat_obj(0u);
x_78 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_77, x_75);
lean::cnstr_set(x_1, 1, x_78);
lean::cnstr_set(x_1, 0, x_76);
return x_1;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_79 = lean::cnstr_get(x_1, 0);
x_80 = lean::cnstr_get(x_1, 1);
lean::inc(x_80);
lean::inc(x_79);
lean::dec(x_1);
x_81 = l_Lean_IR_NormalizeIds_normIndex(x_79, x_2);
lean::dec(x_79);
x_82 = lean::mk_nat_obj(0u);
x_83 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_82, x_80);
x_84 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
case 9:
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_1);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_1, 0);
x_87 = l_Lean_IR_NormalizeIds_normIndex(x_86, x_2);
lean::dec(x_86);
lean::cnstr_set(x_1, 0, x_87);
return x_1;
}
else
{
uint8 x_88; obj* x_89; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_89 = lean::cnstr_get(x_1, 0);
lean::inc(x_89);
lean::dec(x_1);
x_90 = l_Lean_IR_NormalizeIds_normIndex(x_89, x_2);
lean::dec(x_89);
x_91 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_88);
return x_91;
}
}
case 10:
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_1);
if (x_92 == 0)
{
obj* x_93; obj* x_94; 
x_93 = lean::cnstr_get(x_1, 0);
x_94 = l_Lean_IR_NormalizeIds_normIndex(x_93, x_2);
lean::dec(x_93);
lean::cnstr_set(x_1, 0, x_94);
return x_1;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
x_95 = lean::cnstr_get(x_1, 0);
lean::inc(x_95);
lean::dec(x_1);
x_96 = l_Lean_IR_NormalizeIds_normIndex(x_95, x_2);
lean::dec(x_95);
x_97 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
case 11:
{
return x_1;
}
case 12:
{
uint8 x_98; 
x_98 = !lean::is_exclusive(x_1);
if (x_98 == 0)
{
obj* x_99; obj* x_100; 
x_99 = lean::cnstr_get(x_1, 0);
x_100 = l_Lean_IR_NormalizeIds_normIndex(x_99, x_2);
lean::dec(x_99);
lean::cnstr_set(x_1, 0, x_100);
return x_1;
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_1, 0);
lean::inc(x_101);
lean::dec(x_1);
x_102 = l_Lean_IR_NormalizeIds_normIndex(x_101, x_2);
lean::dec(x_101);
x_103 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
default: 
{
uint8 x_104; 
x_104 = !lean::is_exclusive(x_1);
if (x_104 == 0)
{
obj* x_105; obj* x_106; 
x_105 = lean::cnstr_get(x_1, 0);
x_106 = l_Lean_IR_NormalizeIds_normIndex(x_105, x_2);
lean::dec(x_105);
lean::cnstr_set(x_1, 0, x_106);
return x_1;
}
else
{
obj* x_107; obj* x_108; obj* x_109; 
x_107 = lean::cnstr_get(x_1, 0);
lean::inc(x_107);
lean::dec(x_1);
x_108 = l_Lean_IR_NormalizeIds_normIndex(x_107, x_2);
lean::dec(x_107);
x_109 = lean::alloc_cnstr(13, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
}
}
obj* l_Lean_IR_NormalizeIds_normExpr___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normExpr___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normExpr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normExpr___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_normExpr___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_NormalizeIds_normExpr(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_withVar___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::inc(x_4);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean::apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
obj* l_Lean_IR_NormalizeIds_withVar(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withVar___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_IR_NormalizeIds_withJP___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::inc(x_4);
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_3, x_1, x_4);
x_8 = lean::apply_3(x_2, x_4, x_7, x_6);
return x_8;
}
}
obj* l_Lean_IR_NormalizeIds_withJP(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withJP___rarg), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::nat_add(x_5, x_10);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1() {
_start:
{
obj* x_1; uint8 x_2; uint8 x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = 0;
x_3 = 7;
x_4 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_3);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_11);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
x_14 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_6, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
x_18 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1 + 1);
lean::inc(x_16);
lean::dec(x_6);
x_19 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_18);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_2, x_21);
x_23 = lean::array_fset(x_8, x_2, x_20);
lean::dec(x_2);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
obj* l_Lean_IR_NormalizeIds_withParams___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_1, x_1, x_5, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(x_7, x_5, x_1);
x_10 = lean::apply_3(x_2, x_9, x_7, x_8);
return x_10;
}
}
obj* l_Lean_IR_NormalizeIds_withParams(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_withParams___rarg), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_MtoN___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_Lean_IR_NormalizeIds_MtoN(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_MtoN___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::nat_add(x_5, x_10);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_11);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
x_14 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_6, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
x_18 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1 + 1);
lean::inc(x_16);
lean::dec(x_6);
x_19 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_18);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_2, x_21);
x_23 = lean::array_fset(x_8, x_2, x_20);
lean::dec(x_2);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(13);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_10 = lean::array_fset(x_2, x_1, x_9);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_3);
x_13 = l_Lean_IR_NormalizeIds_normFnBody___main(x_12, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
lean::cnstr_set(x_8, 1, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_1, x_16);
x_18 = lean::array_fset(x_10, x_1, x_8);
lean::dec(x_1);
x_1 = x_17;
x_2 = x_18;
x_4 = x_15;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_8, 0);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_8);
lean::inc(x_3);
x_22 = l_Lean_IR_NormalizeIds_normFnBody___main(x_21, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::mk_nat_obj(1u);
x_27 = lean::nat_add(x_1, x_26);
x_28 = lean::array_fset(x_10, x_1, x_25);
lean::dec(x_1);
x_1 = x_27;
x_2 = x_28;
x_4 = x_24;
goto _start;
}
}
else
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_8);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_8, 0);
lean::inc(x_3);
x_32 = l_Lean_IR_NormalizeIds_normFnBody___main(x_31, x_3, x_4);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
lean::cnstr_set(x_8, 0, x_33);
x_35 = lean::mk_nat_obj(1u);
x_36 = lean::nat_add(x_1, x_35);
x_37 = lean::array_fset(x_10, x_1, x_8);
lean::dec(x_1);
x_1 = x_36;
x_2 = x_37;
x_4 = x_34;
goto _start;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_8, 0);
lean::inc(x_39);
lean::dec(x_8);
lean::inc(x_3);
x_40 = l_Lean_IR_NormalizeIds_normFnBody___main(x_39, x_3, x_4);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_41);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_add(x_1, x_44);
x_46 = lean::array_fset(x_10, x_1, x_43);
lean::dec(x_1);
x_1 = x_45;
x_2 = x_46;
x_4 = x_42;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_NormalizeIds_normFnBody___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
x_8 = l_Lean_IR_NormalizeIds_normExpr___main(x_6, x_2);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::inc(x_3);
x_11 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_5, x_3);
x_12 = l_Lean_IR_NormalizeIds_normFnBody___main(x_7, x_11, x_10);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_1, 2, x_14);
lean::cnstr_set(x_1, 1, x_8);
lean::cnstr_set(x_1, 0, x_3);
lean::cnstr_set(x_12, 0, x_1);
return x_12;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 2, x_15);
lean::cnstr_set(x_1, 1, x_8);
lean::cnstr_set(x_1, 0, x_3);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
else
{
obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_20 = lean::cnstr_get(x_1, 1);
x_21 = lean::cnstr_get(x_1, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_18);
lean::dec(x_1);
x_22 = l_Lean_IR_NormalizeIds_normExpr___main(x_20, x_2);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_3, x_23);
lean::inc(x_3);
x_25 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_18, x_3);
x_26 = l_Lean_IR_NormalizeIds_normFnBody___main(x_21, x_25, x_24);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_29 = x_26;
} else {
 lean::dec_ref(x_26);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_27);
lean::cnstr_set_scalar(x_30, sizeof(void*)*3, x_19);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
return x_31;
}
}
case 1:
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_1);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; 
x_33 = lean::cnstr_get(x_1, 0);
x_34 = lean::cnstr_get(x_1, 1);
x_35 = lean::cnstr_get(x_1, 2);
x_36 = lean::cnstr_get(x_1, 3);
x_37 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_38 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_34, x_34, x_37, x_2, x_3);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_41 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_39, x_37, x_34);
x_42 = l_Lean_IR_NormalizeIds_normFnBody___main(x_35, x_39, x_40);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
lean::dec(x_42);
x_45 = lean::mk_nat_obj(1u);
x_46 = lean::nat_add(x_44, x_45);
lean::inc(x_44);
x_47 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_33, x_44);
x_48 = l_Lean_IR_NormalizeIds_normFnBody___main(x_36, x_47, x_46);
x_49 = !lean::is_exclusive(x_48);
if (x_49 == 0)
{
obj* x_50; 
x_50 = lean::cnstr_get(x_48, 0);
lean::cnstr_set(x_1, 3, x_50);
lean::cnstr_set(x_1, 2, x_43);
lean::cnstr_set(x_1, 1, x_41);
lean::cnstr_set(x_1, 0, x_44);
lean::cnstr_set(x_48, 0, x_1);
return x_48;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::cnstr_get(x_48, 0);
x_52 = lean::cnstr_get(x_48, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_48);
lean::cnstr_set(x_1, 3, x_51);
lean::cnstr_set(x_1, 2, x_43);
lean::cnstr_set(x_1, 1, x_41);
lean::cnstr_set(x_1, 0, x_44);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_54 = lean::cnstr_get(x_1, 0);
x_55 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_1, 2);
x_57 = lean::cnstr_get(x_1, 3);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_1);
x_58 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_59 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_55, x_55, x_58, x_2, x_3);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_59, 1);
lean::inc(x_61);
lean::dec(x_59);
x_62 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_60, x_58, x_55);
x_63 = l_Lean_IR_NormalizeIds_normFnBody___main(x_56, x_60, x_61);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
lean::dec(x_63);
x_66 = lean::mk_nat_obj(1u);
x_67 = lean::nat_add(x_65, x_66);
lean::inc(x_65);
x_68 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_2, x_54, x_65);
x_69 = l_Lean_IR_NormalizeIds_normFnBody___main(x_57, x_68, x_67);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_72 = x_69;
} else {
 lean::dec_ref(x_69);
 x_72 = lean::box(0);
}
x_73 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_73, 0, x_65);
lean::cnstr_set(x_73, 1, x_62);
lean::cnstr_set(x_73, 2, x_64);
lean::cnstr_set(x_73, 3, x_70);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_71);
return x_74;
}
}
case 2:
{
uint8 x_75; 
x_75 = !lean::is_exclusive(x_1);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; uint8 x_82; 
x_76 = lean::cnstr_get(x_1, 0);
x_77 = lean::cnstr_get(x_1, 2);
x_78 = lean::cnstr_get(x_1, 3);
x_79 = l_Lean_IR_NormalizeIds_normIndex(x_76, x_2);
lean::dec(x_76);
x_80 = l_Lean_IR_NormalizeIds_normArg___main(x_77, x_2);
x_81 = l_Lean_IR_NormalizeIds_normFnBody___main(x_78, x_2, x_3);
x_82 = !lean::is_exclusive(x_81);
if (x_82 == 0)
{
obj* x_83; 
x_83 = lean::cnstr_get(x_81, 0);
lean::cnstr_set(x_1, 3, x_83);
lean::cnstr_set(x_1, 2, x_80);
lean::cnstr_set(x_1, 0, x_79);
lean::cnstr_set(x_81, 0, x_1);
return x_81;
}
else
{
obj* x_84; obj* x_85; obj* x_86; 
x_84 = lean::cnstr_get(x_81, 0);
x_85 = lean::cnstr_get(x_81, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_81);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set(x_1, 2, x_80);
lean::cnstr_set(x_1, 0, x_79);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_1);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_87 = lean::cnstr_get(x_1, 0);
x_88 = lean::cnstr_get(x_1, 1);
x_89 = lean::cnstr_get(x_1, 2);
x_90 = lean::cnstr_get(x_1, 3);
lean::inc(x_90);
lean::inc(x_89);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_1);
x_91 = l_Lean_IR_NormalizeIds_normIndex(x_87, x_2);
lean::dec(x_87);
x_92 = l_Lean_IR_NormalizeIds_normArg___main(x_89, x_2);
x_93 = l_Lean_IR_NormalizeIds_normFnBody___main(x_90, x_2, x_3);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_93, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_93)) {
 lean::cnstr_release(x_93, 0);
 lean::cnstr_release(x_93, 1);
 x_96 = x_93;
} else {
 lean::dec_ref(x_93);
 x_96 = lean::box(0);
}
x_97 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_97, 0, x_91);
lean::cnstr_set(x_97, 1, x_88);
lean::cnstr_set(x_97, 2, x_92);
lean::cnstr_set(x_97, 3, x_94);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_95);
return x_98;
}
}
case 3:
{
uint8 x_99; 
x_99 = !lean::is_exclusive(x_1);
if (x_99 == 0)
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; uint8 x_104; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_1, 2);
x_102 = l_Lean_IR_NormalizeIds_normIndex(x_100, x_2);
lean::dec(x_100);
x_103 = l_Lean_IR_NormalizeIds_normFnBody___main(x_101, x_2, x_3);
x_104 = !lean::is_exclusive(x_103);
if (x_104 == 0)
{
obj* x_105; 
x_105 = lean::cnstr_get(x_103, 0);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 0, x_102);
lean::cnstr_set(x_103, 0, x_1);
return x_103;
}
else
{
obj* x_106; obj* x_107; obj* x_108; 
x_106 = lean::cnstr_get(x_103, 0);
x_107 = lean::cnstr_get(x_103, 1);
lean::inc(x_107);
lean::inc(x_106);
lean::dec(x_103);
lean::cnstr_set(x_1, 2, x_106);
lean::cnstr_set(x_1, 0, x_102);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_1);
lean::cnstr_set(x_108, 1, x_107);
return x_108;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_109 = lean::cnstr_get(x_1, 0);
x_110 = lean::cnstr_get(x_1, 1);
x_111 = lean::cnstr_get(x_1, 2);
lean::inc(x_111);
lean::inc(x_110);
lean::inc(x_109);
lean::dec(x_1);
x_112 = l_Lean_IR_NormalizeIds_normIndex(x_109, x_2);
lean::dec(x_109);
x_113 = l_Lean_IR_NormalizeIds_normFnBody___main(x_111, x_2, x_3);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_113, 1);
lean::inc(x_115);
if (lean::is_exclusive(x_113)) {
 lean::cnstr_release(x_113, 0);
 lean::cnstr_release(x_113, 1);
 x_116 = x_113;
} else {
 lean::dec_ref(x_113);
 x_116 = lean::box(0);
}
x_117 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_117, 0, x_112);
lean::cnstr_set(x_117, 1, x_110);
lean::cnstr_set(x_117, 2, x_114);
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_115);
return x_118;
}
}
case 4:
{
uint8 x_119; 
x_119 = !lean::is_exclusive(x_1);
if (x_119 == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; uint8 x_126; 
x_120 = lean::cnstr_get(x_1, 0);
x_121 = lean::cnstr_get(x_1, 2);
x_122 = lean::cnstr_get(x_1, 3);
x_123 = l_Lean_IR_NormalizeIds_normIndex(x_120, x_2);
lean::dec(x_120);
x_124 = l_Lean_IR_NormalizeIds_normIndex(x_121, x_2);
lean::dec(x_121);
x_125 = l_Lean_IR_NormalizeIds_normFnBody___main(x_122, x_2, x_3);
x_126 = !lean::is_exclusive(x_125);
if (x_126 == 0)
{
obj* x_127; 
x_127 = lean::cnstr_get(x_125, 0);
lean::cnstr_set(x_1, 3, x_127);
lean::cnstr_set(x_1, 2, x_124);
lean::cnstr_set(x_1, 0, x_123);
lean::cnstr_set(x_125, 0, x_1);
return x_125;
}
else
{
obj* x_128; obj* x_129; obj* x_130; 
x_128 = lean::cnstr_get(x_125, 0);
x_129 = lean::cnstr_get(x_125, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_125);
lean::cnstr_set(x_1, 3, x_128);
lean::cnstr_set(x_1, 2, x_124);
lean::cnstr_set(x_1, 0, x_123);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_1);
lean::cnstr_set(x_130, 1, x_129);
return x_130;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_131 = lean::cnstr_get(x_1, 0);
x_132 = lean::cnstr_get(x_1, 1);
x_133 = lean::cnstr_get(x_1, 2);
x_134 = lean::cnstr_get(x_1, 3);
lean::inc(x_134);
lean::inc(x_133);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_1);
x_135 = l_Lean_IR_NormalizeIds_normIndex(x_131, x_2);
lean::dec(x_131);
x_136 = l_Lean_IR_NormalizeIds_normIndex(x_133, x_2);
lean::dec(x_133);
x_137 = l_Lean_IR_NormalizeIds_normFnBody___main(x_134, x_2, x_3);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_137, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 x_140 = x_137;
} else {
 lean::dec_ref(x_137);
 x_140 = lean::box(0);
}
x_141 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_132);
lean::cnstr_set(x_141, 2, x_136);
lean::cnstr_set(x_141, 3, x_138);
if (lean::is_scalar(x_140)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_140;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_139);
return x_142;
}
}
case 5:
{
uint8 x_143; 
x_143 = !lean::is_exclusive(x_1);
if (x_143 == 0)
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; uint8 x_150; 
x_144 = lean::cnstr_get(x_1, 0);
x_145 = lean::cnstr_get(x_1, 3);
x_146 = lean::cnstr_get(x_1, 4);
x_147 = l_Lean_IR_NormalizeIds_normIndex(x_144, x_2);
lean::dec(x_144);
x_148 = l_Lean_IR_NormalizeIds_normIndex(x_145, x_2);
lean::dec(x_145);
x_149 = l_Lean_IR_NormalizeIds_normFnBody___main(x_146, x_2, x_3);
x_150 = !lean::is_exclusive(x_149);
if (x_150 == 0)
{
obj* x_151; 
x_151 = lean::cnstr_get(x_149, 0);
lean::cnstr_set(x_1, 4, x_151);
lean::cnstr_set(x_1, 3, x_148);
lean::cnstr_set(x_1, 0, x_147);
lean::cnstr_set(x_149, 0, x_1);
return x_149;
}
else
{
obj* x_152; obj* x_153; obj* x_154; 
x_152 = lean::cnstr_get(x_149, 0);
x_153 = lean::cnstr_get(x_149, 1);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_149);
lean::cnstr_set(x_1, 4, x_152);
lean::cnstr_set(x_1, 3, x_148);
lean::cnstr_set(x_1, 0, x_147);
x_154 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_154, 0, x_1);
lean::cnstr_set(x_154, 1, x_153);
return x_154;
}
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; uint8 x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_155 = lean::cnstr_get(x_1, 0);
x_156 = lean::cnstr_get(x_1, 1);
x_157 = lean::cnstr_get(x_1, 2);
x_158 = lean::cnstr_get(x_1, 3);
x_159 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_160 = lean::cnstr_get(x_1, 4);
lean::inc(x_160);
lean::inc(x_158);
lean::inc(x_157);
lean::inc(x_156);
lean::inc(x_155);
lean::dec(x_1);
x_161 = l_Lean_IR_NormalizeIds_normIndex(x_155, x_2);
lean::dec(x_155);
x_162 = l_Lean_IR_NormalizeIds_normIndex(x_158, x_2);
lean::dec(x_158);
x_163 = l_Lean_IR_NormalizeIds_normFnBody___main(x_160, x_2, x_3);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 x_166 = x_163;
} else {
 lean::dec_ref(x_163);
 x_166 = lean::box(0);
}
x_167 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_167, 0, x_161);
lean::cnstr_set(x_167, 1, x_156);
lean::cnstr_set(x_167, 2, x_157);
lean::cnstr_set(x_167, 3, x_162);
lean::cnstr_set(x_167, 4, x_164);
lean::cnstr_set_scalar(x_167, sizeof(void*)*5, x_159);
if (lean::is_scalar(x_166)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_166;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
return x_168;
}
}
case 6:
{
uint8 x_169; 
x_169 = !lean::is_exclusive(x_1);
if (x_169 == 0)
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; uint8 x_174; 
x_170 = lean::cnstr_get(x_1, 0);
x_171 = lean::cnstr_get(x_1, 2);
x_172 = l_Lean_IR_NormalizeIds_normIndex(x_170, x_2);
lean::dec(x_170);
x_173 = l_Lean_IR_NormalizeIds_normFnBody___main(x_171, x_2, x_3);
x_174 = !lean::is_exclusive(x_173);
if (x_174 == 0)
{
obj* x_175; 
x_175 = lean::cnstr_get(x_173, 0);
lean::cnstr_set(x_1, 2, x_175);
lean::cnstr_set(x_1, 0, x_172);
lean::cnstr_set(x_173, 0, x_1);
return x_173;
}
else
{
obj* x_176; obj* x_177; obj* x_178; 
x_176 = lean::cnstr_get(x_173, 0);
x_177 = lean::cnstr_get(x_173, 1);
lean::inc(x_177);
lean::inc(x_176);
lean::dec(x_173);
lean::cnstr_set(x_1, 2, x_176);
lean::cnstr_set(x_1, 0, x_172);
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_1);
lean::cnstr_set(x_178, 1, x_177);
return x_178;
}
}
else
{
obj* x_179; obj* x_180; uint8 x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; 
x_179 = lean::cnstr_get(x_1, 0);
x_180 = lean::cnstr_get(x_1, 1);
x_181 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_182 = lean::cnstr_get(x_1, 2);
lean::inc(x_182);
lean::inc(x_180);
lean::inc(x_179);
lean::dec(x_1);
x_183 = l_Lean_IR_NormalizeIds_normIndex(x_179, x_2);
lean::dec(x_179);
x_184 = l_Lean_IR_NormalizeIds_normFnBody___main(x_182, x_2, x_3);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_186 = lean::cnstr_get(x_184, 1);
lean::inc(x_186);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 x_187 = x_184;
} else {
 lean::dec_ref(x_184);
 x_187 = lean::box(0);
}
x_188 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_188, 0, x_183);
lean::cnstr_set(x_188, 1, x_180);
lean::cnstr_set(x_188, 2, x_185);
lean::cnstr_set_scalar(x_188, sizeof(void*)*3, x_181);
if (lean::is_scalar(x_187)) {
 x_189 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_189 = x_187;
}
lean::cnstr_set(x_189, 0, x_188);
lean::cnstr_set(x_189, 1, x_186);
return x_189;
}
}
case 7:
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_1);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_1, 0);
x_192 = lean::cnstr_get(x_1, 2);
x_193 = l_Lean_IR_NormalizeIds_normIndex(x_191, x_2);
lean::dec(x_191);
x_194 = l_Lean_IR_NormalizeIds_normFnBody___main(x_192, x_2, x_3);
x_195 = !lean::is_exclusive(x_194);
if (x_195 == 0)
{
obj* x_196; 
x_196 = lean::cnstr_get(x_194, 0);
lean::cnstr_set(x_1, 2, x_196);
lean::cnstr_set(x_1, 0, x_193);
lean::cnstr_set(x_194, 0, x_1);
return x_194;
}
else
{
obj* x_197; obj* x_198; obj* x_199; 
x_197 = lean::cnstr_get(x_194, 0);
x_198 = lean::cnstr_get(x_194, 1);
lean::inc(x_198);
lean::inc(x_197);
lean::dec(x_194);
lean::cnstr_set(x_1, 2, x_197);
lean::cnstr_set(x_1, 0, x_193);
x_199 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_199, 0, x_1);
lean::cnstr_set(x_199, 1, x_198);
return x_199;
}
}
else
{
obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_200 = lean::cnstr_get(x_1, 0);
x_201 = lean::cnstr_get(x_1, 1);
x_202 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_203 = lean::cnstr_get(x_1, 2);
lean::inc(x_203);
lean::inc(x_201);
lean::inc(x_200);
lean::dec(x_1);
x_204 = l_Lean_IR_NormalizeIds_normIndex(x_200, x_2);
lean::dec(x_200);
x_205 = l_Lean_IR_NormalizeIds_normFnBody___main(x_203, x_2, x_3);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_207 = lean::cnstr_get(x_205, 1);
lean::inc(x_207);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 lean::cnstr_release(x_205, 1);
 x_208 = x_205;
} else {
 lean::dec_ref(x_205);
 x_208 = lean::box(0);
}
x_209 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_209, 0, x_204);
lean::cnstr_set(x_209, 1, x_201);
lean::cnstr_set(x_209, 2, x_206);
lean::cnstr_set_scalar(x_209, sizeof(void*)*3, x_202);
if (lean::is_scalar(x_208)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_208;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_207);
return x_210;
}
}
case 8:
{
uint8 x_211; 
x_211 = !lean::is_exclusive(x_1);
if (x_211 == 0)
{
obj* x_212; obj* x_213; obj* x_214; obj* x_215; uint8 x_216; 
x_212 = lean::cnstr_get(x_1, 0);
x_213 = lean::cnstr_get(x_1, 1);
x_214 = l_Lean_IR_NormalizeIds_normIndex(x_212, x_2);
lean::dec(x_212);
x_215 = l_Lean_IR_NormalizeIds_normFnBody___main(x_213, x_2, x_3);
x_216 = !lean::is_exclusive(x_215);
if (x_216 == 0)
{
obj* x_217; 
x_217 = lean::cnstr_get(x_215, 0);
lean::cnstr_set(x_1, 1, x_217);
lean::cnstr_set(x_1, 0, x_214);
lean::cnstr_set(x_215, 0, x_1);
return x_215;
}
else
{
obj* x_218; obj* x_219; obj* x_220; 
x_218 = lean::cnstr_get(x_215, 0);
x_219 = lean::cnstr_get(x_215, 1);
lean::inc(x_219);
lean::inc(x_218);
lean::dec(x_215);
lean::cnstr_set(x_1, 1, x_218);
lean::cnstr_set(x_1, 0, x_214);
x_220 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_220, 0, x_1);
lean::cnstr_set(x_220, 1, x_219);
return x_220;
}
}
else
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
x_221 = lean::cnstr_get(x_1, 0);
x_222 = lean::cnstr_get(x_1, 1);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_1);
x_223 = l_Lean_IR_NormalizeIds_normIndex(x_221, x_2);
lean::dec(x_221);
x_224 = l_Lean_IR_NormalizeIds_normFnBody___main(x_222, x_2, x_3);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
x_226 = lean::cnstr_get(x_224, 1);
lean::inc(x_226);
if (lean::is_exclusive(x_224)) {
 lean::cnstr_release(x_224, 0);
 lean::cnstr_release(x_224, 1);
 x_227 = x_224;
} else {
 lean::dec_ref(x_224);
 x_227 = lean::box(0);
}
x_228 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_228, 0, x_223);
lean::cnstr_set(x_228, 1, x_225);
if (lean::is_scalar(x_227)) {
 x_229 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_229 = x_227;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_226);
return x_229;
}
}
case 9:
{
uint8 x_230; 
x_230 = !lean::is_exclusive(x_1);
if (x_230 == 0)
{
obj* x_231; obj* x_232; uint8 x_233; 
x_231 = lean::cnstr_get(x_1, 1);
x_232 = l_Lean_IR_NormalizeIds_normFnBody___main(x_231, x_2, x_3);
x_233 = !lean::is_exclusive(x_232);
if (x_233 == 0)
{
obj* x_234; 
x_234 = lean::cnstr_get(x_232, 0);
lean::cnstr_set(x_1, 1, x_234);
lean::cnstr_set(x_232, 0, x_1);
return x_232;
}
else
{
obj* x_235; obj* x_236; obj* x_237; 
x_235 = lean::cnstr_get(x_232, 0);
x_236 = lean::cnstr_get(x_232, 1);
lean::inc(x_236);
lean::inc(x_235);
lean::dec(x_232);
lean::cnstr_set(x_1, 1, x_235);
x_237 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_237, 0, x_1);
lean::cnstr_set(x_237, 1, x_236);
return x_237;
}
}
else
{
obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_238 = lean::cnstr_get(x_1, 0);
x_239 = lean::cnstr_get(x_1, 1);
lean::inc(x_239);
lean::inc(x_238);
lean::dec(x_1);
x_240 = l_Lean_IR_NormalizeIds_normFnBody___main(x_239, x_2, x_3);
x_241 = lean::cnstr_get(x_240, 0);
lean::inc(x_241);
x_242 = lean::cnstr_get(x_240, 1);
lean::inc(x_242);
if (lean::is_exclusive(x_240)) {
 lean::cnstr_release(x_240, 0);
 lean::cnstr_release(x_240, 1);
 x_243 = x_240;
} else {
 lean::dec_ref(x_240);
 x_243 = lean::box(0);
}
x_244 = lean::alloc_cnstr(9, 2, 0);
lean::cnstr_set(x_244, 0, x_238);
lean::cnstr_set(x_244, 1, x_241);
if (lean::is_scalar(x_243)) {
 x_245 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_245 = x_243;
}
lean::cnstr_set(x_245, 0, x_244);
lean::cnstr_set(x_245, 1, x_242);
return x_245;
}
}
case 10:
{
uint8 x_246; 
x_246 = !lean::is_exclusive(x_1);
if (x_246 == 0)
{
obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; uint8 x_252; 
x_247 = lean::cnstr_get(x_1, 1);
x_248 = lean::cnstr_get(x_1, 2);
x_249 = l_Lean_IR_NormalizeIds_normIndex(x_247, x_2);
lean::dec(x_247);
x_250 = lean::mk_nat_obj(0u);
x_251 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(x_250, x_248, x_2, x_3);
x_252 = !lean::is_exclusive(x_251);
if (x_252 == 0)
{
obj* x_253; 
x_253 = lean::cnstr_get(x_251, 0);
lean::cnstr_set(x_1, 2, x_253);
lean::cnstr_set(x_1, 1, x_249);
lean::cnstr_set(x_251, 0, x_1);
return x_251;
}
else
{
obj* x_254; obj* x_255; obj* x_256; 
x_254 = lean::cnstr_get(x_251, 0);
x_255 = lean::cnstr_get(x_251, 1);
lean::inc(x_255);
lean::inc(x_254);
lean::dec(x_251);
lean::cnstr_set(x_1, 2, x_254);
lean::cnstr_set(x_1, 1, x_249);
x_256 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_256, 0, x_1);
lean::cnstr_set(x_256, 1, x_255);
return x_256;
}
}
else
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; 
x_257 = lean::cnstr_get(x_1, 0);
x_258 = lean::cnstr_get(x_1, 1);
x_259 = lean::cnstr_get(x_1, 2);
lean::inc(x_259);
lean::inc(x_258);
lean::inc(x_257);
lean::dec(x_1);
x_260 = l_Lean_IR_NormalizeIds_normIndex(x_258, x_2);
lean::dec(x_258);
x_261 = lean::mk_nat_obj(0u);
x_262 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(x_261, x_259, x_2, x_3);
x_263 = lean::cnstr_get(x_262, 0);
lean::inc(x_263);
x_264 = lean::cnstr_get(x_262, 1);
lean::inc(x_264);
if (lean::is_exclusive(x_262)) {
 lean::cnstr_release(x_262, 0);
 lean::cnstr_release(x_262, 1);
 x_265 = x_262;
} else {
 lean::dec_ref(x_262);
 x_265 = lean::box(0);
}
x_266 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_266, 0, x_257);
lean::cnstr_set(x_266, 1, x_260);
lean::cnstr_set(x_266, 2, x_263);
if (lean::is_scalar(x_265)) {
 x_267 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_267 = x_265;
}
lean::cnstr_set(x_267, 0, x_266);
lean::cnstr_set(x_267, 1, x_264);
return x_267;
}
}
case 11:
{
uint8 x_268; 
x_268 = !lean::is_exclusive(x_1);
if (x_268 == 0)
{
obj* x_269; obj* x_270; obj* x_271; 
x_269 = lean::cnstr_get(x_1, 0);
x_270 = l_Lean_IR_NormalizeIds_normArg___main(x_269, x_2);
lean::dec(x_2);
lean::cnstr_set(x_1, 0, x_270);
x_271 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_271, 0, x_1);
lean::cnstr_set(x_271, 1, x_3);
return x_271;
}
else
{
obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_272 = lean::cnstr_get(x_1, 0);
lean::inc(x_272);
lean::dec(x_1);
x_273 = l_Lean_IR_NormalizeIds_normArg___main(x_272, x_2);
lean::dec(x_2);
x_274 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
x_275 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_3);
return x_275;
}
}
case 12:
{
uint8 x_276; 
x_276 = !lean::is_exclusive(x_1);
if (x_276 == 0)
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_277 = lean::cnstr_get(x_1, 0);
x_278 = lean::cnstr_get(x_1, 1);
x_279 = l_Lean_IR_NormalizeIds_normIndex(x_277, x_2);
lean::dec(x_277);
x_280 = lean::mk_nat_obj(0u);
x_281 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_280, x_278);
lean::dec(x_2);
lean::cnstr_set(x_1, 1, x_281);
lean::cnstr_set(x_1, 0, x_279);
x_282 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_282, 0, x_1);
lean::cnstr_set(x_282, 1, x_3);
return x_282;
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
x_283 = lean::cnstr_get(x_1, 0);
x_284 = lean::cnstr_get(x_1, 1);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_1);
x_285 = l_Lean_IR_NormalizeIds_normIndex(x_283, x_2);
lean::dec(x_283);
x_286 = lean::mk_nat_obj(0u);
x_287 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_2, x_286, x_284);
lean::dec(x_2);
x_288 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_288, 0, x_285);
lean::cnstr_set(x_288, 1, x_287);
x_289 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_3);
return x_289;
}
}
default: 
{
obj* x_290; 
lean::dec(x_2);
x_290 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_290, 0, x_1);
lean::cnstr_set(x_290, 1, x_3);
return x_290;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_normFnBody(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_NormalizeIds_normFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_12 = lean::nat_add(x_5, x_10);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_14 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_4, x_13, x_5);
x_3 = x_11;
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_11);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
x_14 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; uint8 x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_16 = lean::cnstr_get(x_6, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
x_18 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1 + 1);
lean::inc(x_16);
lean::dec(x_6);
x_19 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1 + 1, x_18);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_2, x_21);
x_23 = lean::array_fset(x_8, x_2, x_20);
lean::dec(x_2);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
obj* l_Lean_IR_NormalizeIds_normDecl___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(x_5, x_5, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(x_9, x_7, x_5);
x_12 = l_Lean_IR_NormalizeIds_normFnBody___main(x_6, x_9, x_10);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_1, 2, x_14);
lean::cnstr_set(x_1, 1, x_11);
lean::cnstr_set(x_12, 0, x_1);
return x_12;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_12);
lean::cnstr_set(x_1, 2, x_15);
lean::cnstr_set(x_1, 1, x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_21 = lean::cnstr_get(x_1, 2);
lean::inc(x_21);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_1);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(x_19, x_19, x_22, x_2, x_3);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_26 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(x_24, x_22, x_19);
x_27 = l_Lean_IR_NormalizeIds_normFnBody___main(x_21, x_24, x_25);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 x_30 = x_27;
} else {
 lean::dec_ref(x_27);
 x_30 = lean::box(0);
}
x_31 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_31, 0, x_18);
lean::cnstr_set(x_31, 1, x_26);
lean::cnstr_set(x_31, 2, x_28);
lean::cnstr_set_scalar(x_31, sizeof(void*)*3, x_20);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
return x_32;
}
}
else
{
obj* x_33; 
lean::dec(x_2);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_3);
return x_33;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_NormalizeIds_normDecl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_NormalizeIds_normDecl___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Decl_normalizeIds(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = l_Lean_IR_NormalizeIds_normDecl___main(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArg___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Lean_IR_MapVars_mapArg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::apply_1(x_1, x_6);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = lean::box(1);
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_6);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_1);
x_13 = lean::apply_1(x_1, x_12);
lean::cnstr_set(x_6, 0, x_13);
x_14 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_6, 0);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_1);
x_17 = lean::apply_1(x_1, x_16);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::array_fset(x_8, x_2, x_18);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_19;
goto _start;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_21;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_5, x_4);
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_2);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_9, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
case 1:
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_2);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_2, 1);
x_14 = lean::apply_1(x_1, x_13);
lean::cnstr_set(x_2, 1, x_14);
return x_2;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_17 = lean::apply_1(x_1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
case 2:
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_2);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_22 = lean::apply_1(x_1, x_20);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_23, x_21);
lean::cnstr_set(x_2, 2, x_24);
lean::cnstr_set(x_2, 0, x_22);
return x_2;
}
else
{
obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_2, 0);
x_26 = lean::cnstr_get(x_2, 1);
x_27 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_28 = lean::cnstr_get(x_2, 2);
lean::inc(x_28);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_2);
lean::inc(x_1);
x_29 = lean::apply_1(x_1, x_25);
x_30 = lean::mk_nat_obj(0u);
x_31 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_30, x_28);
x_32 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_32, 0, x_29);
lean::cnstr_set(x_32, 1, x_26);
lean::cnstr_set(x_32, 2, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_27);
return x_32;
}
}
case 3:
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_2);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_2, 1);
x_35 = lean::apply_1(x_1, x_34);
lean::cnstr_set(x_2, 1, x_35);
return x_2;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_2, 0);
x_37 = lean::cnstr_get(x_2, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_2);
x_38 = lean::apply_1(x_1, x_37);
x_39 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
case 4:
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_2);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_2, 1);
x_42 = lean::apply_1(x_1, x_41);
lean::cnstr_set(x_2, 1, x_42);
return x_2;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_2, 0);
x_44 = lean::cnstr_get(x_2, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_2);
x_45 = lean::apply_1(x_1, x_44);
x_46 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
case 5:
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_2);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_2, 2);
x_49 = lean::apply_1(x_1, x_48);
lean::cnstr_set(x_2, 2, x_49);
return x_2;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_2, 0);
x_51 = lean::cnstr_get(x_2, 1);
x_52 = lean::cnstr_get(x_2, 2);
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_2);
x_53 = lean::apply_1(x_1, x_52);
x_54 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
}
case 6:
{
uint8 x_55; 
x_55 = !lean::is_exclusive(x_2);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_2, 1);
x_57 = lean::mk_nat_obj(0u);
x_58 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_57, x_56);
lean::cnstr_set(x_2, 1, x_58);
return x_2;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_2, 0);
x_60 = lean::cnstr_get(x_2, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_2);
x_61 = lean::mk_nat_obj(0u);
x_62 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_61, x_60);
x_63 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
case 7:
{
uint8 x_64; 
x_64 = !lean::is_exclusive(x_2);
if (x_64 == 0)
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_2, 1);
x_66 = lean::mk_nat_obj(0u);
x_67 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_66, x_65);
lean::cnstr_set(x_2, 1, x_67);
return x_2;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_2, 0);
x_69 = lean::cnstr_get(x_2, 1);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_2);
x_70 = lean::mk_nat_obj(0u);
x_71 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_70, x_69);
x_72 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
}
case 8:
{
uint8 x_73; 
x_73 = !lean::is_exclusive(x_2);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_74 = lean::cnstr_get(x_2, 0);
x_75 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_76 = lean::apply_1(x_1, x_74);
x_77 = lean::mk_nat_obj(0u);
x_78 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_77, x_75);
lean::cnstr_set(x_2, 1, x_78);
lean::cnstr_set(x_2, 0, x_76);
return x_2;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_79 = lean::cnstr_get(x_2, 0);
x_80 = lean::cnstr_get(x_2, 1);
lean::inc(x_80);
lean::inc(x_79);
lean::dec(x_2);
lean::inc(x_1);
x_81 = lean::apply_1(x_1, x_79);
x_82 = lean::mk_nat_obj(0u);
x_83 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_82, x_80);
x_84 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
case 9:
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_2);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_2, 0);
x_87 = lean::apply_1(x_1, x_86);
lean::cnstr_set(x_2, 0, x_87);
return x_2;
}
else
{
uint8 x_88; obj* x_89; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_89 = lean::cnstr_get(x_2, 0);
lean::inc(x_89);
lean::dec(x_2);
x_90 = lean::apply_1(x_1, x_89);
x_91 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_88);
return x_91;
}
}
case 10:
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_2);
if (x_92 == 0)
{
obj* x_93; obj* x_94; 
x_93 = lean::cnstr_get(x_2, 0);
x_94 = lean::apply_1(x_1, x_93);
lean::cnstr_set(x_2, 0, x_94);
return x_2;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
x_95 = lean::cnstr_get(x_2, 0);
lean::inc(x_95);
lean::dec(x_2);
x_96 = lean::apply_1(x_1, x_95);
x_97 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
case 11:
{
lean::dec(x_1);
return x_2;
}
case 12:
{
uint8 x_98; 
x_98 = !lean::is_exclusive(x_2);
if (x_98 == 0)
{
obj* x_99; obj* x_100; 
x_99 = lean::cnstr_get(x_2, 0);
x_100 = lean::apply_1(x_1, x_99);
lean::cnstr_set(x_2, 0, x_100);
return x_2;
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_2, 0);
lean::inc(x_101);
lean::dec(x_2);
x_102 = lean::apply_1(x_1, x_101);
x_103 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
default: 
{
uint8 x_104; 
x_104 = !lean::is_exclusive(x_2);
if (x_104 == 0)
{
obj* x_105; obj* x_106; 
x_105 = lean::cnstr_get(x_2, 0);
x_106 = lean::apply_1(x_1, x_105);
lean::cnstr_set(x_2, 0, x_106);
return x_2;
}
else
{
obj* x_107; obj* x_108; obj* x_109; 
x_107 = lean::cnstr_get(x_2, 0);
lean::inc(x_107);
lean::dec(x_2);
x_108 = lean::apply_1(x_1, x_107);
x_109 = lean::alloc_cnstr(13, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
}
}
}
obj* l_Lean_IR_MapVars_mapExpr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapExpr___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_3, x_2);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_8 = lean::array_fset(x_3, x_2, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_6);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_1);
x_13 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_12);
lean::cnstr_set(x_6, 1, x_13);
x_14 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 0);
x_17 = lean::cnstr_get(x_6, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_1);
x_18 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::array_fset(x_8, x_2, x_19);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_20;
goto _start;
}
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_6);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_6, 0);
lean::inc(x_1);
x_24 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_23);
lean::cnstr_set(x_6, 0, x_24);
x_25 = lean::array_fset(x_8, x_2, x_6);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_25;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_6, 0);
lean::inc(x_27);
lean::dec(x_6);
lean::inc(x_1);
x_28 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::array_fset(x_8, x_2, x_29);
lean::dec(x_2);
x_2 = x_10;
x_3 = x_30;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_6 = l_Lean_IR_MapVars_mapExpr___main(x_1, x_4);
x_7 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_5);
lean::cnstr_set(x_2, 2, x_7);
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_10 = lean::cnstr_get(x_2, 1);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
x_12 = l_Lean_IR_MapVars_mapExpr___main(x_1, x_10);
x_13 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_11);
x_14 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*3, x_9);
return x_14;
}
}
case 1:
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_2);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_2, 2);
x_17 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
x_18 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_16);
x_19 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_17);
lean::cnstr_set(x_2, 3, x_19);
lean::cnstr_set(x_2, 2, x_18);
return x_2;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get(x_2, 1);
x_22 = lean::cnstr_get(x_2, 2);
x_23 = lean::cnstr_get(x_2, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_2);
lean::inc(x_1);
x_24 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_22);
x_25 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_23);
x_26 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_21);
lean::cnstr_set(x_26, 2, x_24);
lean::cnstr_set(x_26, 3, x_25);
return x_26;
}
}
case 2:
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_2);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_2, 0);
x_29 = lean::cnstr_get(x_2, 2);
x_30 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
x_31 = lean::apply_1(x_1, x_28);
lean::inc(x_1);
x_32 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_30);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_29);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_29, 0);
x_35 = lean::apply_1(x_1, x_34);
lean::cnstr_set(x_29, 0, x_35);
lean::cnstr_set(x_2, 3, x_32);
lean::cnstr_set(x_2, 0, x_31);
return x_2;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_29, 0);
lean::inc(x_36);
lean::dec(x_29);
x_37 = lean::apply_1(x_1, x_36);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_2, 3, x_32);
lean::cnstr_set(x_2, 2, x_38);
lean::cnstr_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean::dec(x_1);
lean::cnstr_set(x_2, 3, x_32);
lean::cnstr_set(x_2, 0, x_31);
return x_2;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_2, 0);
x_40 = lean::cnstr_get(x_2, 1);
x_41 = lean::cnstr_get(x_2, 2);
x_42 = lean::cnstr_get(x_2, 3);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_2);
lean::inc(x_1);
x_43 = lean::apply_1(x_1, x_39);
lean::inc(x_1);
x_44 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_42);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_41, 0);
lean::inc(x_45);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_46 = x_41;
} else {
 lean::dec_ref(x_41);
 x_46 = lean::box(0);
}
x_47 = lean::apply_1(x_1, x_45);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_40);
lean::cnstr_set(x_49, 2, x_48);
lean::cnstr_set(x_49, 3, x_44);
return x_49;
}
else
{
obj* x_50; 
lean::dec(x_1);
x_50 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_50, 0, x_43);
lean::cnstr_set(x_50, 1, x_40);
lean::cnstr_set(x_50, 2, x_41);
lean::cnstr_set(x_50, 3, x_44);
return x_50;
}
}
}
case 3:
{
uint8 x_51; 
x_51 = !lean::is_exclusive(x_2);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_2, 0);
x_53 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_54 = lean::apply_1(x_1, x_52);
x_55 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_53);
lean::cnstr_set(x_2, 2, x_55);
lean::cnstr_set(x_2, 0, x_54);
return x_2;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = lean::cnstr_get(x_2, 0);
x_57 = lean::cnstr_get(x_2, 1);
x_58 = lean::cnstr_get(x_2, 2);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_2);
lean::inc(x_1);
x_59 = lean::apply_1(x_1, x_56);
x_60 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_58);
x_61 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_57);
lean::cnstr_set(x_61, 2, x_60);
return x_61;
}
}
case 4:
{
uint8 x_62; 
x_62 = !lean::is_exclusive(x_2);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_2, 0);
x_64 = lean::cnstr_get(x_2, 2);
x_65 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
x_66 = lean::apply_1(x_1, x_63);
lean::inc(x_1);
x_67 = lean::apply_1(x_1, x_64);
x_68 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_65);
lean::cnstr_set(x_2, 3, x_68);
lean::cnstr_set(x_2, 2, x_67);
lean::cnstr_set(x_2, 0, x_66);
return x_2;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_69 = lean::cnstr_get(x_2, 0);
x_70 = lean::cnstr_get(x_2, 1);
x_71 = lean::cnstr_get(x_2, 2);
x_72 = lean::cnstr_get(x_2, 3);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::dec(x_2);
lean::inc(x_1);
x_73 = lean::apply_1(x_1, x_69);
lean::inc(x_1);
x_74 = lean::apply_1(x_1, x_71);
x_75 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_72);
x_76 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_74);
lean::cnstr_set(x_76, 3, x_75);
return x_76;
}
}
case 5:
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_2);
if (x_77 == 0)
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_2, 0);
x_79 = lean::cnstr_get(x_2, 3);
x_80 = lean::cnstr_get(x_2, 4);
lean::inc(x_1);
x_81 = lean::apply_1(x_1, x_78);
lean::inc(x_1);
x_82 = lean::apply_1(x_1, x_79);
x_83 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_80);
lean::cnstr_set(x_2, 4, x_83);
lean::cnstr_set(x_2, 3, x_82);
lean::cnstr_set(x_2, 0, x_81);
return x_2;
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_84 = lean::cnstr_get(x_2, 0);
x_85 = lean::cnstr_get(x_2, 1);
x_86 = lean::cnstr_get(x_2, 2);
x_87 = lean::cnstr_get(x_2, 3);
x_88 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_89 = lean::cnstr_get(x_2, 4);
lean::inc(x_89);
lean::inc(x_87);
lean::inc(x_86);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_2);
lean::inc(x_1);
x_90 = lean::apply_1(x_1, x_84);
lean::inc(x_1);
x_91 = lean::apply_1(x_1, x_87);
x_92 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_89);
x_93 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set(x_93, 1, x_85);
lean::cnstr_set(x_93, 2, x_86);
lean::cnstr_set(x_93, 3, x_91);
lean::cnstr_set(x_93, 4, x_92);
lean::cnstr_set_scalar(x_93, sizeof(void*)*5, x_88);
return x_93;
}
}
case 6:
{
uint8 x_94; 
x_94 = !lean::is_exclusive(x_2);
if (x_94 == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_95 = lean::cnstr_get(x_2, 0);
x_96 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_97 = lean::apply_1(x_1, x_95);
x_98 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_96);
lean::cnstr_set(x_2, 2, x_98);
lean::cnstr_set(x_2, 0, x_97);
return x_2;
}
else
{
obj* x_99; obj* x_100; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_2, 0);
x_100 = lean::cnstr_get(x_2, 1);
x_101 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_102 = lean::cnstr_get(x_2, 2);
lean::inc(x_102);
lean::inc(x_100);
lean::inc(x_99);
lean::dec(x_2);
lean::inc(x_1);
x_103 = lean::apply_1(x_1, x_99);
x_104 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_102);
x_105 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_100);
lean::cnstr_set(x_105, 2, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*3, x_101);
return x_105;
}
}
case 7:
{
uint8 x_106; 
x_106 = !lean::is_exclusive(x_2);
if (x_106 == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_107 = lean::cnstr_get(x_2, 0);
x_108 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_109 = lean::apply_1(x_1, x_107);
x_110 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_108);
lean::cnstr_set(x_2, 2, x_110);
lean::cnstr_set(x_2, 0, x_109);
return x_2;
}
else
{
obj* x_111; obj* x_112; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_111 = lean::cnstr_get(x_2, 0);
x_112 = lean::cnstr_get(x_2, 1);
x_113 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_114 = lean::cnstr_get(x_2, 2);
lean::inc(x_114);
lean::inc(x_112);
lean::inc(x_111);
lean::dec(x_2);
lean::inc(x_1);
x_115 = lean::apply_1(x_1, x_111);
x_116 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_114);
x_117 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_112);
lean::cnstr_set(x_117, 2, x_116);
lean::cnstr_set_scalar(x_117, sizeof(void*)*3, x_113);
return x_117;
}
}
case 8:
{
uint8 x_118; 
x_118 = !lean::is_exclusive(x_2);
if (x_118 == 0)
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_119 = lean::cnstr_get(x_2, 0);
x_120 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_121 = lean::apply_1(x_1, x_119);
x_122 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_120);
lean::cnstr_set(x_2, 1, x_122);
lean::cnstr_set(x_2, 0, x_121);
return x_2;
}
else
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_123 = lean::cnstr_get(x_2, 0);
x_124 = lean::cnstr_get(x_2, 1);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_2);
lean::inc(x_1);
x_125 = lean::apply_1(x_1, x_123);
x_126 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_124);
x_127 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_126);
return x_127;
}
}
case 9:
{
uint8 x_128; 
x_128 = !lean::is_exclusive(x_2);
if (x_128 == 0)
{
obj* x_129; obj* x_130; 
x_129 = lean::cnstr_get(x_2, 1);
x_130 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_129);
lean::cnstr_set(x_2, 1, x_130);
return x_2;
}
else
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_131 = lean::cnstr_get(x_2, 0);
x_132 = lean::cnstr_get(x_2, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_2);
x_133 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_132);
x_134 = lean::alloc_cnstr(9, 2, 0);
lean::cnstr_set(x_134, 0, x_131);
lean::cnstr_set(x_134, 1, x_133);
return x_134;
}
}
case 10:
{
uint8 x_135; 
x_135 = !lean::is_exclusive(x_2);
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_136 = lean::cnstr_get(x_2, 1);
x_137 = lean::cnstr_get(x_2, 2);
lean::inc(x_1);
x_138 = lean::apply_1(x_1, x_136);
x_139 = lean::mk_nat_obj(0u);
x_140 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(x_1, x_139, x_137);
lean::cnstr_set(x_2, 2, x_140);
lean::cnstr_set(x_2, 1, x_138);
return x_2;
}
else
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_141 = lean::cnstr_get(x_2, 0);
x_142 = lean::cnstr_get(x_2, 1);
x_143 = lean::cnstr_get(x_2, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::inc(x_141);
lean::dec(x_2);
lean::inc(x_1);
x_144 = lean::apply_1(x_1, x_142);
x_145 = lean::mk_nat_obj(0u);
x_146 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapFnBody___main___spec__1(x_1, x_145, x_143);
x_147 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_147, 0, x_141);
lean::cnstr_set(x_147, 1, x_144);
lean::cnstr_set(x_147, 2, x_146);
return x_147;
}
}
case 11:
{
uint8 x_148; 
x_148 = !lean::is_exclusive(x_2);
if (x_148 == 0)
{
obj* x_149; 
x_149 = lean::cnstr_get(x_2, 0);
if (lean::obj_tag(x_149) == 0)
{
uint8 x_150; 
x_150 = !lean::is_exclusive(x_149);
if (x_150 == 0)
{
obj* x_151; obj* x_152; 
x_151 = lean::cnstr_get(x_149, 0);
x_152 = lean::apply_1(x_1, x_151);
lean::cnstr_set(x_149, 0, x_152);
return x_2;
}
else
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = lean::cnstr_get(x_149, 0);
lean::inc(x_153);
lean::dec(x_149);
x_154 = lean::apply_1(x_1, x_153);
x_155 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_2, 0, x_155);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
else
{
obj* x_156; 
x_156 = lean::cnstr_get(x_2, 0);
lean::inc(x_156);
lean::dec(x_2);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 x_158 = x_156;
} else {
 lean::dec_ref(x_156);
 x_158 = lean::box(0);
}
x_159 = lean::apply_1(x_1, x_157);
if (lean::is_scalar(x_158)) {
 x_160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_160 = x_158;
}
lean::cnstr_set(x_160, 0, x_159);
x_161 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_161, 0, x_160);
return x_161;
}
else
{
obj* x_162; 
lean::dec(x_1);
x_162 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_162, 0, x_156);
return x_162;
}
}
}
case 12:
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_2);
if (x_163 == 0)
{
obj* x_164; obj* x_165; obj* x_166; 
x_164 = lean::cnstr_get(x_2, 1);
x_165 = lean::mk_nat_obj(0u);
x_166 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_165, x_164);
lean::cnstr_set(x_2, 1, x_166);
return x_2;
}
else
{
obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_167 = lean::cnstr_get(x_2, 0);
x_168 = lean::cnstr_get(x_2, 1);
lean::inc(x_168);
lean::inc(x_167);
lean::dec(x_2);
x_169 = lean::mk_nat_obj(0u);
x_170 = l_Array_hmmapAux___main___at_Lean_IR_MapVars_mapArgs___spec__1(x_1, x_169, x_168);
x_171 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_171, 0, x_167);
lean::cnstr_set(x_171, 1, x_170);
return x_171;
}
}
default: 
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Lean_IR_MapVars_mapFnBody(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_FnBody_mapVars(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_MapVars_mapFnBody___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_6, x_5);
lean::cnstr_set(x_3, 1, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_3);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_10, x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
case 1:
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; uint8 x_15; 
x_14 = lean::cnstr_get(x_3, 1);
x_15 = lean::nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_14);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
else
{
obj* x_16; obj* x_17; uint8 x_18; 
x_16 = lean::cnstr_get(x_3, 0);
x_17 = lean::cnstr_get(x_3, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_3);
x_18 = lean::nat_dec_eq(x_1, x_17);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_2);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
else
{
obj* x_20; 
lean::dec(x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
}
}
}
case 2:
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_3);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 2);
x_24 = lean::nat_dec_eq(x_1, x_22);
x_25 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_26 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_25, x_23);
if (x_24 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 2, x_26);
return x_3;
}
else
{
lean::dec(x_22);
lean::cnstr_set(x_3, 2, x_26);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_27; obj* x_28; uint8 x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_3, 0);
x_28 = lean::cnstr_get(x_3, 1);
x_29 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_30 = lean::cnstr_get(x_3, 2);
lean::inc(x_30);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_3);
x_31 = lean::nat_dec_eq(x_1, x_27);
x_32 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_33 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_32, x_30);
if (x_31 == 0)
{
obj* x_34; 
lean::dec(x_2);
x_34 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_34, 0, x_27);
lean::cnstr_set(x_34, 1, x_28);
lean::cnstr_set(x_34, 2, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*3, x_29);
return x_34;
}
else
{
obj* x_35; 
lean::dec(x_27);
x_35 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_35, 0, x_2);
lean::cnstr_set(x_35, 1, x_28);
lean::cnstr_set(x_35, 2, x_33);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_29);
return x_35;
}
}
}
case 3:
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_3);
if (x_36 == 0)
{
obj* x_37; uint8 x_38; 
x_37 = lean::cnstr_get(x_3, 1);
x_38 = lean::nat_dec_eq(x_1, x_37);
if (x_38 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_37);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
else
{
obj* x_39; obj* x_40; uint8 x_41; 
x_39 = lean::cnstr_get(x_3, 0);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_3);
x_41 = lean::nat_dec_eq(x_1, x_40);
if (x_41 == 0)
{
obj* x_42; 
lean::dec(x_2);
x_42 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
else
{
obj* x_43; 
lean::dec(x_40);
x_43 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_2);
return x_43;
}
}
}
case 4:
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_3);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = lean::cnstr_get(x_3, 1);
x_46 = lean::nat_dec_eq(x_1, x_45);
if (x_46 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_45);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
else
{
obj* x_47; obj* x_48; uint8 x_49; 
x_47 = lean::cnstr_get(x_3, 0);
x_48 = lean::cnstr_get(x_3, 1);
lean::inc(x_48);
lean::inc(x_47);
lean::dec(x_3);
x_49 = lean::nat_dec_eq(x_1, x_48);
if (x_49 == 0)
{
obj* x_50; 
lean::dec(x_2);
x_50 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
return x_50;
}
else
{
obj* x_51; 
lean::dec(x_48);
x_51 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set(x_51, 1, x_2);
return x_51;
}
}
}
case 5:
{
uint8 x_52; 
x_52 = !lean::is_exclusive(x_3);
if (x_52 == 0)
{
obj* x_53; uint8 x_54; 
x_53 = lean::cnstr_get(x_3, 2);
x_54 = lean::nat_dec_eq(x_1, x_53);
if (x_54 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_53);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_55 = lean::cnstr_get(x_3, 0);
x_56 = lean::cnstr_get(x_3, 1);
x_57 = lean::cnstr_get(x_3, 2);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_3);
x_58 = lean::nat_dec_eq(x_1, x_57);
if (x_58 == 0)
{
obj* x_59; 
lean::dec(x_2);
x_59 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
}
else
{
obj* x_60; 
lean::dec(x_57);
x_60 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_60, 0, x_55);
lean::cnstr_set(x_60, 1, x_56);
lean::cnstr_set(x_60, 2, x_2);
return x_60;
}
}
}
case 6:
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_3);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::cnstr_get(x_3, 1);
x_63 = lean::mk_nat_obj(0u);
x_64 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_63, x_62);
lean::cnstr_set(x_3, 1, x_64);
return x_3;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_65 = lean::cnstr_get(x_3, 0);
x_66 = lean::cnstr_get(x_3, 1);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_3);
x_67 = lean::mk_nat_obj(0u);
x_68 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_67, x_66);
x_69 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
}
}
case 7:
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_3);
if (x_70 == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_3, 1);
x_72 = lean::mk_nat_obj(0u);
x_73 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_72, x_71);
lean::cnstr_set(x_3, 1, x_73);
return x_3;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_74 = lean::cnstr_get(x_3, 0);
x_75 = lean::cnstr_get(x_3, 1);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_3);
x_76 = lean::mk_nat_obj(0u);
x_77 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_76, x_75);
x_78 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set(x_78, 1, x_77);
return x_78;
}
}
case 8:
{
uint8 x_79; 
x_79 = !lean::is_exclusive(x_3);
if (x_79 == 0)
{
obj* x_80; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; 
x_80 = lean::cnstr_get(x_3, 0);
x_81 = lean::cnstr_get(x_3, 1);
x_82 = lean::nat_dec_eq(x_1, x_80);
x_83 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_84 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_83, x_81);
if (x_82 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 1, x_84);
return x_3;
}
else
{
lean::dec(x_80);
lean::cnstr_set(x_3, 1, x_84);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_85; obj* x_86; uint8 x_87; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_3, 0);
x_86 = lean::cnstr_get(x_3, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_3);
x_87 = lean::nat_dec_eq(x_1, x_85);
x_88 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_89 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_88, x_86);
if (x_87 == 0)
{
obj* x_90; 
lean::dec(x_2);
x_90 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_90, 0, x_85);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
else
{
obj* x_91; 
lean::dec(x_85);
x_91 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_91, 0, x_2);
lean::cnstr_set(x_91, 1, x_89);
return x_91;
}
}
}
case 9:
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_3);
if (x_92 == 0)
{
obj* x_93; uint8 x_94; 
x_93 = lean::cnstr_get(x_3, 0);
x_94 = lean::nat_dec_eq(x_1, x_93);
if (x_94 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_93);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
uint8 x_95; obj* x_96; uint8 x_97; 
x_95 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
x_96 = lean::cnstr_get(x_3, 0);
lean::inc(x_96);
lean::dec(x_3);
x_97 = lean::nat_dec_eq(x_1, x_96);
if (x_97 == 0)
{
obj* x_98; 
lean::dec(x_2);
x_98 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_95);
return x_98;
}
else
{
obj* x_99; 
lean::dec(x_96);
x_99 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_99, 0, x_2);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_95);
return x_99;
}
}
}
case 10:
{
uint8 x_100; 
x_100 = !lean::is_exclusive(x_3);
if (x_100 == 0)
{
obj* x_101; uint8 x_102; 
x_101 = lean::cnstr_get(x_3, 0);
x_102 = lean::nat_dec_eq(x_1, x_101);
if (x_102 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_101);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_103; uint8 x_104; 
x_103 = lean::cnstr_get(x_3, 0);
lean::inc(x_103);
lean::dec(x_3);
x_104 = lean::nat_dec_eq(x_1, x_103);
if (x_104 == 0)
{
obj* x_105; 
lean::dec(x_2);
x_105 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_105, 0, x_103);
return x_105;
}
else
{
obj* x_106; 
lean::dec(x_103);
x_106 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_106, 0, x_2);
return x_106;
}
}
}
case 11:
{
lean::dec(x_2);
return x_3;
}
case 12:
{
uint8 x_107; 
x_107 = !lean::is_exclusive(x_3);
if (x_107 == 0)
{
obj* x_108; uint8 x_109; 
x_108 = lean::cnstr_get(x_3, 0);
x_109 = lean::nat_dec_eq(x_1, x_108);
if (x_109 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_108);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_110; uint8 x_111; 
x_110 = lean::cnstr_get(x_3, 0);
lean::inc(x_110);
lean::dec(x_3);
x_111 = lean::nat_dec_eq(x_1, x_110);
if (x_111 == 0)
{
obj* x_112; 
lean::dec(x_2);
x_112 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_112, 0, x_110);
return x_112;
}
else
{
obj* x_113; 
lean::dec(x_110);
x_113 = lean::alloc_cnstr(12, 1, 0);
lean::cnstr_set(x_113, 0, x_2);
return x_113;
}
}
}
default: 
{
uint8 x_114; 
x_114 = !lean::is_exclusive(x_3);
if (x_114 == 0)
{
obj* x_115; uint8 x_116; 
x_115 = lean::cnstr_get(x_3, 0);
x_116 = lean::nat_dec_eq(x_1, x_115);
if (x_116 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_115);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_117; uint8 x_118; 
x_117 = lean::cnstr_get(x_3, 0);
lean::inc(x_117);
lean::dec(x_3);
x_118 = lean::nat_dec_eq(x_1, x_117);
if (x_118 == 0)
{
obj* x_119; 
lean::dec(x_2);
x_119 = lean::alloc_cnstr(13, 1, 0);
lean::cnstr_set(x_119, 0, x_117);
return x_119;
}
else
{
obj* x_120; 
lean::dec(x_117);
x_120 = lean::alloc_cnstr(13, 1, 0);
lean::cnstr_set(x_120, 0, x_2);
return x_120;
}
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_2);
x_14 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_13);
lean::cnstr_set(x_7, 1, x_14);
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = lean::cnstr_get(x_7, 0);
x_18 = lean::cnstr_get(x_7, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_7);
lean::inc(x_2);
x_19 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::array_fset(x_9, x_3, x_20);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_21;
goto _start;
}
}
else
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_7);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_7, 0);
lean::inc(x_2);
x_25 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_24);
lean::cnstr_set(x_7, 0, x_25);
x_26 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_26;
goto _start;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_7, 0);
lean::inc(x_28);
lean::dec(x_7);
lean::inc(x_2);
x_29 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::array_fset(x_9, x_3, x_30);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_31;
goto _start;
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(1);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::inc(x_2);
lean::cnstr_set(x_7, 0, x_2);
x_17 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_17;
goto _start;
}
}
else
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::nat_dec_eq(x_1, x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_19);
x_22 = lean::array_fset(x_9, x_3, x_21);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_22;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::array_fset(x_9, x_3, x_24);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_25;
goto _start;
}
}
}
else
{
obj* x_27; obj* x_28; 
x_27 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_2);
x_7 = l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_5);
x_8 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_6);
lean::cnstr_set(x_3, 2, x_8);
lean::cnstr_set(x_3, 1, x_7);
return x_3;
}
else
{
obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_11 = lean::cnstr_get(x_3, 1);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_2);
x_13 = l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_11);
x_14 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_12);
x_15 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set(x_15, 2, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*3, x_10);
return x_15;
}
}
case 1:
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_3);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_3, 2);
x_18 = lean::cnstr_get(x_3, 3);
lean::inc(x_2);
x_19 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_17);
x_20 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_18);
lean::cnstr_set(x_3, 3, x_20);
lean::cnstr_set(x_3, 2, x_19);
return x_3;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_3, 0);
x_22 = lean::cnstr_get(x_3, 1);
x_23 = lean::cnstr_get(x_3, 2);
x_24 = lean::cnstr_get(x_3, 3);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_3);
lean::inc(x_2);
x_25 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_23);
x_26 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_24);
x_27 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_22);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
case 2:
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_3);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_3, 0);
x_30 = lean::cnstr_get(x_3, 2);
x_31 = lean::cnstr_get(x_3, 3);
x_32 = lean::nat_dec_eq(x_1, x_29);
lean::inc(x_2);
x_33 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_31);
if (x_32 == 0)
{
if (lean::obj_tag(x_30) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_30);
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
x_35 = lean::cnstr_get(x_30, 0);
x_36 = lean::nat_dec_eq(x_1, x_35);
if (x_36 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 3, x_33);
return x_3;
}
else
{
lean::dec(x_35);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_3, 3, x_33);
return x_3;
}
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::cnstr_get(x_30, 0);
lean::inc(x_37);
lean::dec(x_30);
x_38 = lean::nat_dec_eq(x_1, x_37);
if (x_38 == 0)
{
obj* x_39; 
lean::dec(x_2);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 2, x_39);
return x_3;
}
else
{
obj* x_40; 
lean::dec(x_37);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 2, x_40);
return x_3;
}
}
}
else
{
lean::dec(x_2);
lean::cnstr_set(x_3, 3, x_33);
return x_3;
}
}
else
{
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_30);
if (x_41 == 0)
{
obj* x_42; uint8 x_43; 
x_42 = lean::cnstr_get(x_30, 0);
x_43 = lean::nat_dec_eq(x_1, x_42);
if (x_43 == 0)
{
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
lean::dec(x_42);
lean::inc(x_2);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_44; uint8 x_45; 
x_44 = lean::cnstr_get(x_30, 0);
lean::inc(x_44);
lean::dec(x_30);
x_45 = lean::nat_dec_eq(x_1, x_44);
if (x_45 == 0)
{
obj* x_46; 
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 2, x_46);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
obj* x_47; 
lean::dec(x_44);
lean::inc(x_2);
x_47 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_47, 0, x_2);
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 2, x_47);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
lean::cnstr_set(x_3, 3, x_33);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_3, 0);
x_49 = lean::cnstr_get(x_3, 1);
x_50 = lean::cnstr_get(x_3, 2);
x_51 = lean::cnstr_get(x_3, 3);
lean::inc(x_51);
lean::inc(x_50);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_3);
x_52 = lean::nat_dec_eq(x_1, x_48);
lean::inc(x_2);
x_53 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_51);
if (x_52 == 0)
{
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; obj* x_55; uint8 x_56; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_55 = x_50;
} else {
 lean::dec_ref(x_50);
 x_55 = lean::box(0);
}
x_56 = lean::nat_dec_eq(x_1, x_54);
if (x_56 == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_2);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_54);
x_58 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_58, 0, x_48);
lean::cnstr_set(x_58, 1, x_49);
lean::cnstr_set(x_58, 2, x_57);
lean::cnstr_set(x_58, 3, x_53);
return x_58;
}
else
{
obj* x_59; obj* x_60; 
lean::dec(x_54);
if (lean::is_scalar(x_55)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_55;
}
lean::cnstr_set(x_59, 0, x_2);
x_60 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_60, 0, x_48);
lean::cnstr_set(x_60, 1, x_49);
lean::cnstr_set(x_60, 2, x_59);
lean::cnstr_set(x_60, 3, x_53);
return x_60;
}
}
else
{
obj* x_61; 
lean::dec(x_2);
x_61 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_61, 0, x_48);
lean::cnstr_set(x_61, 1, x_49);
lean::cnstr_set(x_61, 2, x_50);
lean::cnstr_set(x_61, 3, x_53);
return x_61;
}
}
else
{
lean::dec(x_48);
if (lean::obj_tag(x_50) == 0)
{
obj* x_62; obj* x_63; uint8 x_64; 
x_62 = lean::cnstr_get(x_50, 0);
lean::inc(x_62);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_63 = x_50;
} else {
 lean::dec_ref(x_50);
 x_63 = lean::box(0);
}
x_64 = lean::nat_dec_eq(x_1, x_62);
if (x_64 == 0)
{
obj* x_65; obj* x_66; 
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_66, 0, x_2);
lean::cnstr_set(x_66, 1, x_49);
lean::cnstr_set(x_66, 2, x_65);
lean::cnstr_set(x_66, 3, x_53);
return x_66;
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_62);
lean::inc(x_2);
if (lean::is_scalar(x_63)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_63;
}
lean::cnstr_set(x_67, 0, x_2);
x_68 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_68, 0, x_2);
lean::cnstr_set(x_68, 1, x_49);
lean::cnstr_set(x_68, 2, x_67);
lean::cnstr_set(x_68, 3, x_53);
return x_68;
}
}
else
{
obj* x_69; 
x_69 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_69, 0, x_2);
lean::cnstr_set(x_69, 1, x_49);
lean::cnstr_set(x_69, 2, x_50);
lean::cnstr_set(x_69, 3, x_53);
return x_69;
}
}
}
}
case 3:
{
uint8 x_70; 
x_70 = !lean::is_exclusive(x_3);
if (x_70 == 0)
{
obj* x_71; obj* x_72; uint8 x_73; obj* x_74; 
x_71 = lean::cnstr_get(x_3, 0);
x_72 = lean::cnstr_get(x_3, 2);
x_73 = lean::nat_dec_eq(x_1, x_71);
lean::inc(x_2);
x_74 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_72);
if (x_73 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 2, x_74);
return x_3;
}
else
{
lean::dec(x_71);
lean::cnstr_set(x_3, 2, x_74);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; uint8 x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_3, 0);
x_76 = lean::cnstr_get(x_3, 1);
x_77 = lean::cnstr_get(x_3, 2);
lean::inc(x_77);
lean::inc(x_76);
lean::inc(x_75);
lean::dec(x_3);
x_78 = lean::nat_dec_eq(x_1, x_75);
lean::inc(x_2);
x_79 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_77);
if (x_78 == 0)
{
obj* x_80; 
lean::dec(x_2);
x_80 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_80, 0, x_75);
lean::cnstr_set(x_80, 1, x_76);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
else
{
obj* x_81; 
lean::dec(x_75);
x_81 = lean::alloc_cnstr(3, 3, 0);
lean::cnstr_set(x_81, 0, x_2);
lean::cnstr_set(x_81, 1, x_76);
lean::cnstr_set(x_81, 2, x_79);
return x_81;
}
}
}
case 4:
{
uint8 x_82; 
x_82 = !lean::is_exclusive(x_3);
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; uint8 x_86; uint8 x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_3, 0);
x_84 = lean::cnstr_get(x_3, 2);
x_85 = lean::cnstr_get(x_3, 3);
x_86 = lean::nat_dec_eq(x_1, x_83);
x_87 = lean::nat_dec_eq(x_1, x_84);
lean::inc(x_2);
x_88 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_85);
if (x_86 == 0)
{
if (x_87 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 3, x_88);
return x_3;
}
else
{
lean::dec(x_84);
lean::cnstr_set(x_3, 3, x_88);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
else
{
lean::dec(x_83);
if (x_87 == 0)
{
lean::cnstr_set(x_3, 3, x_88);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
lean::dec(x_84);
lean::inc(x_2);
lean::cnstr_set(x_3, 3, x_88);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; uint8 x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_3, 0);
x_90 = lean::cnstr_get(x_3, 1);
x_91 = lean::cnstr_get(x_3, 2);
x_92 = lean::cnstr_get(x_3, 3);
lean::inc(x_92);
lean::inc(x_91);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_3);
x_93 = lean::nat_dec_eq(x_1, x_89);
x_94 = lean::nat_dec_eq(x_1, x_91);
lean::inc(x_2);
x_95 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_92);
if (x_93 == 0)
{
if (x_94 == 0)
{
obj* x_96; 
lean::dec(x_2);
x_96 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_96, 0, x_89);
lean::cnstr_set(x_96, 1, x_90);
lean::cnstr_set(x_96, 2, x_91);
lean::cnstr_set(x_96, 3, x_95);
return x_96;
}
else
{
obj* x_97; 
lean::dec(x_91);
x_97 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_97, 0, x_89);
lean::cnstr_set(x_97, 1, x_90);
lean::cnstr_set(x_97, 2, x_2);
lean::cnstr_set(x_97, 3, x_95);
return x_97;
}
}
else
{
lean::dec(x_89);
if (x_94 == 0)
{
obj* x_98; 
x_98 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_98, 0, x_2);
lean::cnstr_set(x_98, 1, x_90);
lean::cnstr_set(x_98, 2, x_91);
lean::cnstr_set(x_98, 3, x_95);
return x_98;
}
else
{
obj* x_99; 
lean::dec(x_91);
lean::inc(x_2);
x_99 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_99, 0, x_2);
lean::cnstr_set(x_99, 1, x_90);
lean::cnstr_set(x_99, 2, x_2);
lean::cnstr_set(x_99, 3, x_95);
return x_99;
}
}
}
}
case 5:
{
uint8 x_100; 
x_100 = !lean::is_exclusive(x_3);
if (x_100 == 0)
{
obj* x_101; obj* x_102; obj* x_103; uint8 x_104; uint8 x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_3, 0);
x_102 = lean::cnstr_get(x_3, 3);
x_103 = lean::cnstr_get(x_3, 4);
x_104 = lean::nat_dec_eq(x_1, x_101);
x_105 = lean::nat_dec_eq(x_1, x_102);
lean::inc(x_2);
x_106 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_103);
if (x_104 == 0)
{
if (x_105 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 4, x_106);
return x_3;
}
else
{
lean::dec(x_102);
lean::cnstr_set(x_3, 4, x_106);
lean::cnstr_set(x_3, 3, x_2);
return x_3;
}
}
else
{
lean::dec(x_101);
if (x_105 == 0)
{
lean::cnstr_set(x_3, 4, x_106);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
lean::dec(x_102);
lean::inc(x_2);
lean::cnstr_set(x_3, 4, x_106);
lean::cnstr_set(x_3, 3, x_2);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; uint8 x_111; obj* x_112; uint8 x_113; uint8 x_114; obj* x_115; 
x_107 = lean::cnstr_get(x_3, 0);
x_108 = lean::cnstr_get(x_3, 1);
x_109 = lean::cnstr_get(x_3, 2);
x_110 = lean::cnstr_get(x_3, 3);
x_111 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*5);
x_112 = lean::cnstr_get(x_3, 4);
lean::inc(x_112);
lean::inc(x_110);
lean::inc(x_109);
lean::inc(x_108);
lean::inc(x_107);
lean::dec(x_3);
x_113 = lean::nat_dec_eq(x_1, x_107);
x_114 = lean::nat_dec_eq(x_1, x_110);
lean::inc(x_2);
x_115 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_112);
if (x_113 == 0)
{
if (x_114 == 0)
{
obj* x_116; 
lean::dec(x_2);
x_116 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_116, 0, x_107);
lean::cnstr_set(x_116, 1, x_108);
lean::cnstr_set(x_116, 2, x_109);
lean::cnstr_set(x_116, 3, x_110);
lean::cnstr_set(x_116, 4, x_115);
lean::cnstr_set_scalar(x_116, sizeof(void*)*5, x_111);
return x_116;
}
else
{
obj* x_117; 
lean::dec(x_110);
x_117 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_117, 0, x_107);
lean::cnstr_set(x_117, 1, x_108);
lean::cnstr_set(x_117, 2, x_109);
lean::cnstr_set(x_117, 3, x_2);
lean::cnstr_set(x_117, 4, x_115);
lean::cnstr_set_scalar(x_117, sizeof(void*)*5, x_111);
return x_117;
}
}
else
{
lean::dec(x_107);
if (x_114 == 0)
{
obj* x_118; 
x_118 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_118, 0, x_2);
lean::cnstr_set(x_118, 1, x_108);
lean::cnstr_set(x_118, 2, x_109);
lean::cnstr_set(x_118, 3, x_110);
lean::cnstr_set(x_118, 4, x_115);
lean::cnstr_set_scalar(x_118, sizeof(void*)*5, x_111);
return x_118;
}
else
{
obj* x_119; 
lean::dec(x_110);
lean::inc(x_2);
x_119 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_119, 0, x_2);
lean::cnstr_set(x_119, 1, x_108);
lean::cnstr_set(x_119, 2, x_109);
lean::cnstr_set(x_119, 3, x_2);
lean::cnstr_set(x_119, 4, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*5, x_111);
return x_119;
}
}
}
}
case 6:
{
uint8 x_120; 
x_120 = !lean::is_exclusive(x_3);
if (x_120 == 0)
{
obj* x_121; obj* x_122; uint8 x_123; obj* x_124; 
x_121 = lean::cnstr_get(x_3, 0);
x_122 = lean::cnstr_get(x_3, 2);
x_123 = lean::nat_dec_eq(x_1, x_121);
lean::inc(x_2);
x_124 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_122);
if (x_123 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 2, x_124);
return x_3;
}
else
{
lean::dec(x_121);
lean::cnstr_set(x_3, 2, x_124);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_125; obj* x_126; uint8 x_127; obj* x_128; uint8 x_129; obj* x_130; 
x_125 = lean::cnstr_get(x_3, 0);
x_126 = lean::cnstr_get(x_3, 1);
x_127 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_128 = lean::cnstr_get(x_3, 2);
lean::inc(x_128);
lean::inc(x_126);
lean::inc(x_125);
lean::dec(x_3);
x_129 = lean::nat_dec_eq(x_1, x_125);
lean::inc(x_2);
x_130 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_128);
if (x_129 == 0)
{
obj* x_131; 
lean::dec(x_2);
x_131 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_131, 0, x_125);
lean::cnstr_set(x_131, 1, x_126);
lean::cnstr_set(x_131, 2, x_130);
lean::cnstr_set_scalar(x_131, sizeof(void*)*3, x_127);
return x_131;
}
else
{
obj* x_132; 
lean::dec(x_125);
x_132 = lean::alloc_cnstr(6, 3, 1);
lean::cnstr_set(x_132, 0, x_2);
lean::cnstr_set(x_132, 1, x_126);
lean::cnstr_set(x_132, 2, x_130);
lean::cnstr_set_scalar(x_132, sizeof(void*)*3, x_127);
return x_132;
}
}
}
case 7:
{
uint8 x_133; 
x_133 = !lean::is_exclusive(x_3);
if (x_133 == 0)
{
obj* x_134; obj* x_135; uint8 x_136; obj* x_137; 
x_134 = lean::cnstr_get(x_3, 0);
x_135 = lean::cnstr_get(x_3, 2);
x_136 = lean::nat_dec_eq(x_1, x_134);
lean::inc(x_2);
x_137 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_135);
if (x_136 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 2, x_137);
return x_3;
}
else
{
lean::dec(x_134);
lean::cnstr_set(x_3, 2, x_137);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_138; obj* x_139; uint8 x_140; obj* x_141; uint8 x_142; obj* x_143; 
x_138 = lean::cnstr_get(x_3, 0);
x_139 = lean::cnstr_get(x_3, 1);
x_140 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_141 = lean::cnstr_get(x_3, 2);
lean::inc(x_141);
lean::inc(x_139);
lean::inc(x_138);
lean::dec(x_3);
x_142 = lean::nat_dec_eq(x_1, x_138);
lean::inc(x_2);
x_143 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_141);
if (x_142 == 0)
{
obj* x_144; 
lean::dec(x_2);
x_144 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_144, 0, x_138);
lean::cnstr_set(x_144, 1, x_139);
lean::cnstr_set(x_144, 2, x_143);
lean::cnstr_set_scalar(x_144, sizeof(void*)*3, x_140);
return x_144;
}
else
{
obj* x_145; 
lean::dec(x_138);
x_145 = lean::alloc_cnstr(7, 3, 1);
lean::cnstr_set(x_145, 0, x_2);
lean::cnstr_set(x_145, 1, x_139);
lean::cnstr_set(x_145, 2, x_143);
lean::cnstr_set_scalar(x_145, sizeof(void*)*3, x_140);
return x_145;
}
}
}
case 8:
{
uint8 x_146; 
x_146 = !lean::is_exclusive(x_3);
if (x_146 == 0)
{
obj* x_147; obj* x_148; uint8 x_149; obj* x_150; 
x_147 = lean::cnstr_get(x_3, 0);
x_148 = lean::cnstr_get(x_3, 1);
x_149 = lean::nat_dec_eq(x_1, x_147);
lean::inc(x_2);
x_150 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_148);
if (x_149 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 1, x_150);
return x_3;
}
else
{
lean::dec(x_147);
lean::cnstr_set(x_3, 1, x_150);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
else
{
obj* x_151; obj* x_152; uint8 x_153; obj* x_154; 
x_151 = lean::cnstr_get(x_3, 0);
x_152 = lean::cnstr_get(x_3, 1);
lean::inc(x_152);
lean::inc(x_151);
lean::dec(x_3);
x_153 = lean::nat_dec_eq(x_1, x_151);
lean::inc(x_2);
x_154 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_152);
if (x_153 == 0)
{
obj* x_155; 
lean::dec(x_2);
x_155 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set(x_155, 1, x_154);
return x_155;
}
else
{
obj* x_156; 
lean::dec(x_151);
x_156 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_156, 0, x_2);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
}
}
case 9:
{
uint8 x_157; 
x_157 = !lean::is_exclusive(x_3);
if (x_157 == 0)
{
obj* x_158; obj* x_159; 
x_158 = lean::cnstr_get(x_3, 1);
x_159 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_158);
lean::cnstr_set(x_3, 1, x_159);
return x_3;
}
else
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_160 = lean::cnstr_get(x_3, 0);
x_161 = lean::cnstr_get(x_3, 1);
lean::inc(x_161);
lean::inc(x_160);
lean::dec(x_3);
x_162 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_161);
x_163 = lean::alloc_cnstr(9, 2, 0);
lean::cnstr_set(x_163, 0, x_160);
lean::cnstr_set(x_163, 1, x_162);
return x_163;
}
}
case 10:
{
uint8 x_164; 
x_164 = !lean::is_exclusive(x_3);
if (x_164 == 0)
{
obj* x_165; obj* x_166; uint8 x_167; obj* x_168; obj* x_169; 
x_165 = lean::cnstr_get(x_3, 1);
x_166 = lean::cnstr_get(x_3, 2);
x_167 = lean::nat_dec_eq(x_1, x_165);
x_168 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_169 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_168, x_166);
if (x_167 == 0)
{
lean::dec(x_2);
lean::cnstr_set(x_3, 2, x_169);
return x_3;
}
else
{
lean::dec(x_165);
lean::cnstr_set(x_3, 2, x_169);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
else
{
obj* x_170; obj* x_171; obj* x_172; uint8 x_173; obj* x_174; obj* x_175; 
x_170 = lean::cnstr_get(x_3, 0);
x_171 = lean::cnstr_get(x_3, 1);
x_172 = lean::cnstr_get(x_3, 2);
lean::inc(x_172);
lean::inc(x_171);
lean::inc(x_170);
lean::dec(x_3);
x_173 = lean::nat_dec_eq(x_1, x_171);
x_174 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_175 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_174, x_172);
if (x_173 == 0)
{
obj* x_176; 
lean::dec(x_2);
x_176 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_176, 0, x_170);
lean::cnstr_set(x_176, 1, x_171);
lean::cnstr_set(x_176, 2, x_175);
return x_176;
}
else
{
obj* x_177; 
lean::dec(x_171);
x_177 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_177, 0, x_170);
lean::cnstr_set(x_177, 1, x_2);
lean::cnstr_set(x_177, 2, x_175);
return x_177;
}
}
}
case 11:
{
uint8 x_178; 
x_178 = !lean::is_exclusive(x_3);
if (x_178 == 0)
{
obj* x_179; 
x_179 = lean::cnstr_get(x_3, 0);
if (lean::obj_tag(x_179) == 0)
{
uint8 x_180; 
x_180 = !lean::is_exclusive(x_179);
if (x_180 == 0)
{
obj* x_181; uint8 x_182; 
x_181 = lean::cnstr_get(x_179, 0);
x_182 = lean::nat_dec_eq(x_1, x_181);
if (x_182 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
lean::dec(x_181);
lean::cnstr_set(x_179, 0, x_2);
return x_3;
}
}
else
{
obj* x_183; uint8 x_184; 
x_183 = lean::cnstr_get(x_179, 0);
lean::inc(x_183);
lean::dec(x_179);
x_184 = lean::nat_dec_eq(x_1, x_183);
if (x_184 == 0)
{
obj* x_185; 
lean::dec(x_2);
x_185 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_185, 0, x_183);
lean::cnstr_set(x_3, 0, x_185);
return x_3;
}
else
{
obj* x_186; 
lean::dec(x_183);
x_186 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_186, 0, x_2);
lean::cnstr_set(x_3, 0, x_186);
return x_3;
}
}
}
else
{
lean::dec(x_2);
return x_3;
}
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_3, 0);
lean::inc(x_187);
lean::dec(x_3);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_189; uint8 x_190; 
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_189 = x_187;
} else {
 lean::dec_ref(x_187);
 x_189 = lean::box(0);
}
x_190 = lean::nat_dec_eq(x_1, x_188);
if (x_190 == 0)
{
obj* x_191; obj* x_192; 
lean::dec(x_2);
if (lean::is_scalar(x_189)) {
 x_191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_191 = x_189;
}
lean::cnstr_set(x_191, 0, x_188);
x_192 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_192, 0, x_191);
return x_192;
}
else
{
obj* x_193; obj* x_194; 
lean::dec(x_188);
if (lean::is_scalar(x_189)) {
 x_193 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_193 = x_189;
}
lean::cnstr_set(x_193, 0, x_2);
x_194 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_194, 0, x_193);
return x_194;
}
}
else
{
obj* x_195; 
lean::dec(x_2);
x_195 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_195, 0, x_187);
return x_195;
}
}
}
case 12:
{
uint8 x_196; 
x_196 = !lean::is_exclusive(x_3);
if (x_196 == 0)
{
obj* x_197; obj* x_198; obj* x_199; 
x_197 = lean::cnstr_get(x_3, 1);
x_198 = lean::mk_nat_obj(0u);
x_199 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_198, x_197);
lean::cnstr_set(x_3, 1, x_199);
return x_3;
}
else
{
obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_200 = lean::cnstr_get(x_3, 0);
x_201 = lean::cnstr_get(x_3, 1);
lean::inc(x_201);
lean::inc(x_200);
lean::dec(x_3);
x_202 = lean::mk_nat_obj(0u);
x_203 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_202, x_201);
x_204 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_204, 0, x_200);
lean::cnstr_set(x_204, 1, x_203);
return x_204;
}
}
default: 
{
lean::dec(x_2);
return x_3;
}
}
}
}
obj* l_Lean_IR_FnBody_replaceVar(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__4(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__3(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__6(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__5(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__8(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__7(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__10(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__9(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__12(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__11(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapExpr___main___at_Lean_IR_FnBody_replaceVar___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__13(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_replaceVar___spec__15(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapArgs___at_Lean_IR_FnBody_replaceVar___spec__14(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_FnBody_replaceVar___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_FnBody_replaceVar(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
