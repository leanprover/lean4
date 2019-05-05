// Lean compiler output
// Module: init.lean.compiler.ir.normids
// Imports: init.lean.compiler.ir.basic init.control.reader
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
obj* l_Lean_IR_NormalizeIds_withVar___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_MtoN(obj*);
obj* l_Lean_IR_NormalizeIds_normVar___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withVar___boxed(obj*);
obj* l_Lean_IR_NormalizeIds_normDecl___main(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normVar(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normDecl(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_NormalizeIds_normJP___boxed(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normJP(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_IR_NormalizeIds_normArgs(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normArg___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normExpr___main(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_normIndex___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withParams___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP(obj*);
obj* l_Lean_IR_NormalizeIds_MtoN___rarg(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_mkFresh(obj*);
obj* l_Lean_IR_NormalizeIds_normIndex(obj*, obj*);
obj* l_Lean_IR_NormalizeIds_MtoN___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normDecl___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_mkFresh___boxed(obj*);
obj* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_withJP___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_withParams___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_NormalizeIds_mkFresh___rarg(obj*);
obj* l_Lean_IR_NormalizeIds_withVar(obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; 
x_10 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_12 = x_0;
} else {
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = l_Lean_IR_NormalizeIds_normIndex(x_10, x_1);
lean::dec(x_10);
if (lean::is_scalar(x_12)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_12;
}
lean::cnstr_set(x_15, 0, x_13);
return x_15;
}
case 2:
{
obj* x_16; obj* x_18; uint8 x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_16 = lean::cnstr_get(x_0, 0);
x_18 = lean::cnstr_get(x_0, 1);
x_20 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_21 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_23 = x_0;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_21);
 lean::dec(x_0);
 x_23 = lean::box(0);
}
lean::inc(x_1);
x_25 = l_Lean_IR_NormalizeIds_normIndex(x_16, x_1);
lean::dec(x_16);
x_27 = lean::mk_nat_obj(0ul);
x_28 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_27, x_21);
if (lean::is_scalar(x_23)) {
 x_29 = lean::alloc_cnstr(2, 3, 1);
} else {
 x_29 = x_23;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_18);
lean::cnstr_set(x_29, 2, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*3, x_20);
x_30 = x_29;
return x_30;
}
case 3:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; 
x_31 = lean::cnstr_get(x_0, 0);
x_33 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_35 = x_0;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_0);
 x_35 = lean::box(0);
}
x_36 = l_Lean_IR_NormalizeIds_normIndex(x_33, x_1);
lean::dec(x_33);
if (lean::is_scalar(x_35)) {
 x_38 = lean::alloc_cnstr(3, 2, 0);
} else {
 x_38 = x_35;
}
lean::cnstr_set(x_38, 0, x_31);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
case 4:
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
x_39 = lean::cnstr_get(x_0, 0);
x_41 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_43 = x_0;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::dec(x_0);
 x_43 = lean::box(0);
}
x_44 = l_Lean_IR_NormalizeIds_normIndex(x_41, x_1);
lean::dec(x_41);
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(4, 2, 0);
} else {
 x_46 = x_43;
}
lean::cnstr_set(x_46, 0, x_39);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
case 5:
{
obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_56; 
x_47 = lean::cnstr_get(x_0, 0);
x_49 = lean::cnstr_get(x_0, 1);
x_51 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_53 = x_0;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_0);
 x_53 = lean::box(0);
}
x_54 = l_Lean_IR_NormalizeIds_normIndex(x_51, x_1);
lean::dec(x_51);
if (lean::is_scalar(x_53)) {
 x_56 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_56 = x_53;
}
lean::cnstr_set(x_56, 0, x_47);
lean::cnstr_set(x_56, 1, x_49);
lean::cnstr_set(x_56, 2, x_54);
return x_56;
}
case 6:
{
obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_57 = lean::cnstr_get(x_0, 0);
x_59 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_61 = x_0;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_0);
 x_61 = lean::box(0);
}
x_62 = lean::mk_nat_obj(0ul);
x_63 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_62, x_59);
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(6, 2, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_57);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
case 7:
{
obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_65 = lean::cnstr_get(x_0, 0);
x_67 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_69 = x_0;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_0);
 x_69 = lean::box(0);
}
x_70 = lean::mk_nat_obj(0ul);
x_71 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_70, x_67);
if (lean::is_scalar(x_69)) {
 x_72 = lean::alloc_cnstr(7, 2, 0);
} else {
 x_72 = x_69;
}
lean::cnstr_set(x_72, 0, x_65);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
case 8:
{
obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
x_73 = lean::cnstr_get(x_0, 0);
x_75 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_77 = x_0;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_0);
 x_77 = lean::box(0);
}
lean::inc(x_1);
x_79 = l_Lean_IR_NormalizeIds_normIndex(x_73, x_1);
lean::dec(x_73);
x_81 = lean::mk_nat_obj(0ul);
x_82 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_81, x_75);
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_79);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
case 9:
{
uint8 x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_84 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_85 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_87 = x_0;
} else {
 lean::inc(x_85);
 lean::dec(x_0);
 x_87 = lean::box(0);
}
x_88 = l_Lean_IR_NormalizeIds_normIndex(x_85, x_1);
lean::dec(x_85);
if (lean::is_scalar(x_87)) {
 x_90 = lean::alloc_cnstr(9, 1, 1);
} else {
 x_90 = x_87;
}
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set_scalar(x_90, sizeof(void*)*1, x_84);
x_91 = x_90;
return x_91;
}
case 10:
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; 
x_92 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_94 = x_0;
} else {
 lean::inc(x_92);
 lean::dec(x_0);
 x_94 = lean::box(0);
}
x_95 = l_Lean_IR_NormalizeIds_normIndex(x_92, x_1);
lean::dec(x_92);
if (lean::is_scalar(x_94)) {
 x_97 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_97 = x_94;
}
lean::cnstr_set(x_97, 0, x_95);
return x_97;
}
case 11:
{
lean::dec(x_1);
return x_0;
}
case 12:
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; 
x_99 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_101 = x_0;
} else {
 lean::inc(x_99);
 lean::dec(x_0);
 x_101 = lean::box(0);
}
x_102 = l_Lean_IR_NormalizeIds_normIndex(x_99, x_1);
lean::dec(x_99);
if (lean::is_scalar(x_101)) {
 x_104 = lean::alloc_cnstr(12, 1, 0);
} else {
 x_104 = x_101;
}
lean::cnstr_set(x_104, 0, x_102);
return x_104;
}
default:
{
obj* x_105; obj* x_107; obj* x_108; obj* x_110; 
x_105 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_107 = x_0;
} else {
 lean::inc(x_105);
 lean::dec(x_0);
 x_107 = lean::box(0);
}
x_108 = l_Lean_IR_NormalizeIds_normIndex(x_105, x_1);
lean::dec(x_105);
if (lean::is_scalar(x_107)) {
 x_110 = lean::alloc_cnstr(13, 1, 0);
} else {
 x_110 = x_107;
}
lean::cnstr_set(x_110, 0, x_108);
return x_110;
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
obj* l_Lean_IR_NormalizeIds_mkFresh___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::nat_add(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_IR_NormalizeIds_mkFresh(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_NormalizeIds_mkFresh___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_NormalizeIds_mkFresh___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_NormalizeIds_mkFresh(x_0);
lean::dec(x_0);
return x_1;
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
x_0 = lean::box(12);
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
obj* x_26; obj* x_28; uint8 x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_26 = lean::cnstr_get(x_0, 0);
x_28 = lean::cnstr_get(x_0, 1);
x_30 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
x_31 = lean::cnstr_get(x_0, 2);
x_33 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_35 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_0);
 x_35 = lean::box(0);
}
x_36 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_38 = l_Array_miterateAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__1(x_28, x_28, x_36, x_1, x_2);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
lean::inc(x_39);
x_45 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__2(x_39, x_36, x_28);
x_46 = l_Lean_IR_NormalizeIds_normFnBody___main(x_31, x_39, x_41);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::mk_nat_obj(1ul);
x_53 = lean::nat_add(x_49, x_52);
lean::inc(x_49);
x_55 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_26, x_49);
x_56 = l_Lean_IR_NormalizeIds_normFnBody___main(x_33, x_55, x_53);
x_57 = lean::cnstr_get(x_56, 0);
x_59 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_61 = x_56;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_35;
}
lean::cnstr_set(x_62, 0, x_49);
lean::cnstr_set(x_62, 1, x_45);
lean::cnstr_set(x_62, 2, x_47);
lean::cnstr_set(x_62, 3, x_57);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_30);
x_63 = x_62;
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_59);
return x_64;
}
case 2:
{
obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
x_65 = lean::cnstr_get(x_0, 0);
x_67 = lean::cnstr_get(x_0, 1);
x_69 = lean::cnstr_get(x_0, 2);
x_71 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_73 = x_0;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_0);
 x_73 = lean::box(0);
}
lean::inc(x_1);
x_75 = l_Lean_IR_NormalizeIds_normIndex(x_65, x_1);
lean::dec(x_65);
lean::inc(x_1);
x_78 = l_Lean_IR_NormalizeIds_normIndex(x_69, x_1);
lean::dec(x_69);
x_80 = l_Lean_IR_NormalizeIds_normFnBody___main(x_71, x_1, x_2);
x_81 = lean::cnstr_get(x_80, 0);
x_83 = lean::cnstr_get(x_80, 1);
if (lean::is_exclusive(x_80)) {
 x_85 = x_80;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_80);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_86 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_86 = x_73;
}
lean::cnstr_set(x_86, 0, x_75);
lean::cnstr_set(x_86, 1, x_67);
lean::cnstr_set(x_86, 2, x_78);
lean::cnstr_set(x_86, 3, x_81);
if (lean::is_scalar(x_85)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_85;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_83);
return x_87;
}
case 3:
{
obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_98; obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
x_88 = lean::cnstr_get(x_0, 0);
x_90 = lean::cnstr_get(x_0, 1);
x_92 = lean::cnstr_get(x_0, 2);
x_94 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_96 = x_0;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_0);
 x_96 = lean::box(0);
}
lean::inc(x_1);
x_98 = l_Lean_IR_NormalizeIds_normIndex(x_88, x_1);
lean::dec(x_88);
lean::inc(x_1);
x_101 = l_Lean_IR_NormalizeIds_normIndex(x_92, x_1);
lean::dec(x_92);
x_103 = l_Lean_IR_NormalizeIds_normFnBody___main(x_94, x_1, x_2);
x_104 = lean::cnstr_get(x_103, 0);
x_106 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 x_108 = x_103;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_103);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_109 = lean::alloc_cnstr(3, 4, 0);
} else {
 x_109 = x_96;
}
lean::cnstr_set(x_109, 0, x_98);
lean::cnstr_set(x_109, 1, x_90);
lean::cnstr_set(x_109, 2, x_101);
lean::cnstr_set(x_109, 3, x_104);
if (lean::is_scalar(x_108)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_108;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_106);
return x_110;
}
case 4:
{
obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_111 = lean::cnstr_get(x_0, 0);
x_113 = lean::cnstr_get(x_0, 1);
x_115 = lean::cnstr_get(x_0, 2);
x_117 = lean::cnstr_get(x_0, 3);
x_119 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
x_120 = lean::cnstr_get(x_0, 4);
if (lean::is_exclusive(x_0)) {
 x_122 = x_0;
} else {
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::inc(x_117);
 lean::inc(x_120);
 lean::dec(x_0);
 x_122 = lean::box(0);
}
lean::inc(x_1);
x_124 = l_Lean_IR_NormalizeIds_normIndex(x_111, x_1);
lean::dec(x_111);
lean::inc(x_1);
x_127 = l_Lean_IR_NormalizeIds_normIndex(x_117, x_1);
lean::dec(x_117);
x_129 = l_Lean_IR_NormalizeIds_normFnBody___main(x_120, x_1, x_2);
x_130 = lean::cnstr_get(x_129, 0);
x_132 = lean::cnstr_get(x_129, 1);
if (lean::is_exclusive(x_129)) {
 x_134 = x_129;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_129);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_135 = lean::alloc_cnstr(4, 5, 1);
} else {
 x_135 = x_122;
}
lean::cnstr_set(x_135, 0, x_124);
lean::cnstr_set(x_135, 1, x_113);
lean::cnstr_set(x_135, 2, x_115);
lean::cnstr_set(x_135, 3, x_127);
lean::cnstr_set(x_135, 4, x_130);
lean::cnstr_set_scalar(x_135, sizeof(void*)*5, x_119);
x_136 = x_135;
if (lean::is_scalar(x_134)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_134;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_132);
return x_137;
}
case 5:
{
obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_153; obj* x_154; obj* x_155; 
x_138 = lean::cnstr_get(x_0, 0);
x_140 = lean::cnstr_get(x_0, 1);
x_142 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_144 = x_0;
} else {
 lean::inc(x_138);
 lean::inc(x_140);
 lean::inc(x_142);
 lean::dec(x_0);
 x_144 = lean::box(0);
}
lean::inc(x_1);
x_146 = l_Lean_IR_NormalizeIds_normIndex(x_138, x_1);
lean::dec(x_138);
x_148 = l_Lean_IR_NormalizeIds_normFnBody___main(x_142, x_1, x_2);
x_149 = lean::cnstr_get(x_148, 0);
x_151 = lean::cnstr_get(x_148, 1);
if (lean::is_exclusive(x_148)) {
 x_153 = x_148;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::dec(x_148);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_154 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_154 = x_144;
}
lean::cnstr_set(x_154, 0, x_146);
lean::cnstr_set(x_154, 1, x_140);
lean::cnstr_set(x_154, 2, x_149);
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_151);
return x_155;
}
case 6:
{
obj* x_156; obj* x_158; uint8 x_160; obj* x_161; obj* x_163; obj* x_165; obj* x_167; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_156 = lean::cnstr_get(x_0, 0);
x_158 = lean::cnstr_get(x_0, 1);
x_160 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_161 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_163 = x_0;
} else {
 lean::inc(x_156);
 lean::inc(x_158);
 lean::inc(x_161);
 lean::dec(x_0);
 x_163 = lean::box(0);
}
lean::inc(x_1);
x_165 = l_Lean_IR_NormalizeIds_normIndex(x_156, x_1);
lean::dec(x_156);
x_167 = l_Lean_IR_NormalizeIds_normFnBody___main(x_161, x_1, x_2);
x_168 = lean::cnstr_get(x_167, 0);
x_170 = lean::cnstr_get(x_167, 1);
if (lean::is_exclusive(x_167)) {
 x_172 = x_167;
} else {
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_167);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_173 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_173 = x_163;
}
lean::cnstr_set(x_173, 0, x_165);
lean::cnstr_set(x_173, 1, x_158);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set_scalar(x_173, sizeof(void*)*3, x_160);
x_174 = x_173;
if (lean::is_scalar(x_172)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_172;
}
lean::cnstr_set(x_175, 0, x_174);
lean::cnstr_set(x_175, 1, x_170);
return x_175;
}
case 7:
{
obj* x_176; obj* x_178; uint8 x_180; obj* x_181; obj* x_183; obj* x_185; obj* x_187; obj* x_188; obj* x_190; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_176 = lean::cnstr_get(x_0, 0);
x_178 = lean::cnstr_get(x_0, 1);
x_180 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_181 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_183 = x_0;
} else {
 lean::inc(x_176);
 lean::inc(x_178);
 lean::inc(x_181);
 lean::dec(x_0);
 x_183 = lean::box(0);
}
lean::inc(x_1);
x_185 = l_Lean_IR_NormalizeIds_normIndex(x_176, x_1);
lean::dec(x_176);
x_187 = l_Lean_IR_NormalizeIds_normFnBody___main(x_181, x_1, x_2);
x_188 = lean::cnstr_get(x_187, 0);
x_190 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 x_192 = x_187;
} else {
 lean::inc(x_188);
 lean::inc(x_190);
 lean::dec(x_187);
 x_192 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_193 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_193 = x_183;
}
lean::cnstr_set(x_193, 0, x_185);
lean::cnstr_set(x_193, 1, x_178);
lean::cnstr_set(x_193, 2, x_188);
lean::cnstr_set_scalar(x_193, sizeof(void*)*3, x_180);
x_194 = x_193;
if (lean::is_scalar(x_192)) {
 x_195 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_195 = x_192;
}
lean::cnstr_set(x_195, 0, x_194);
lean::cnstr_set(x_195, 1, x_190);
return x_195;
}
case 8:
{
obj* x_196; obj* x_198; obj* x_200; obj* x_201; obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_208; 
x_196 = lean::cnstr_get(x_0, 0);
x_198 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_200 = x_0;
} else {
 lean::inc(x_196);
 lean::inc(x_198);
 lean::dec(x_0);
 x_200 = lean::box(0);
}
x_201 = l_Lean_IR_NormalizeIds_normFnBody___main(x_198, x_1, x_2);
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
if (lean::is_scalar(x_200)) {
 x_207 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_207 = x_200;
}
lean::cnstr_set(x_207, 0, x_196);
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
obj* x_209; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_221; obj* x_223; obj* x_225; obj* x_226; obj* x_227; 
x_209 = lean::cnstr_get(x_0, 0);
x_211 = lean::cnstr_get(x_0, 1);
x_213 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_215 = x_0;
} else {
 lean::inc(x_209);
 lean::inc(x_211);
 lean::inc(x_213);
 lean::dec(x_0);
 x_215 = lean::box(0);
}
lean::inc(x_1);
x_217 = l_Lean_IR_NormalizeIds_normIndex(x_211, x_1);
lean::dec(x_211);
x_219 = lean::mk_nat_obj(0ul);
x_220 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3(x_219, x_213, x_1, x_2);
x_221 = lean::cnstr_get(x_220, 0);
x_223 = lean::cnstr_get(x_220, 1);
if (lean::is_exclusive(x_220)) {
 x_225 = x_220;
} else {
 lean::inc(x_221);
 lean::inc(x_223);
 lean::dec(x_220);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_226 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_226 = x_215;
}
lean::cnstr_set(x_226, 0, x_209);
lean::cnstr_set(x_226, 1, x_217);
lean::cnstr_set(x_226, 2, x_221);
if (lean::is_scalar(x_225)) {
 x_227 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_227 = x_225;
}
lean::cnstr_set(x_227, 0, x_226);
lean::cnstr_set(x_227, 1, x_223);
return x_227;
}
case 10:
{
obj* x_228; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_228 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_230 = x_0;
} else {
 lean::inc(x_228);
 lean::dec(x_0);
 x_230 = lean::box(0);
}
x_231 = l_Lean_IR_NormalizeIds_normArg___main(x_228, x_1);
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(10, 1, 0);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_231);
x_233 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_2);
return x_233;
}
case 11:
{
obj* x_234; obj* x_236; obj* x_238; obj* x_240; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_234 = lean::cnstr_get(x_0, 0);
x_236 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_238 = x_0;
} else {
 lean::inc(x_234);
 lean::inc(x_236);
 lean::dec(x_0);
 x_238 = lean::box(0);
}
lean::inc(x_1);
x_240 = l_Lean_IR_NormalizeIds_normIndex(x_234, x_1);
lean::dec(x_234);
x_242 = lean::mk_nat_obj(0ul);
x_243 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normArgs___spec__1(x_1, x_242, x_236);
if (lean::is_scalar(x_238)) {
 x_244 = lean::alloc_cnstr(11, 2, 0);
} else {
 x_244 = x_238;
}
lean::cnstr_set(x_244, 0, x_240);
lean::cnstr_set(x_244, 1, x_243);
x_245 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_245, 0, x_244);
lean::cnstr_set(x_245, 1, x_2);
return x_245;
}
default:
{
obj* x_247; 
lean::dec(x_1);
x_247 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_247, 0, x_0);
lean::cnstr_set(x_247, 1, x_2);
return x_247;
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
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_control_reader(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_normids(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1);
 l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_normFnBody___main___spec__3___closed__1);
return w;
}
