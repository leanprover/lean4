// Lean compiler output
// Module: init.lean.compiler.ir.boxing
// Imports: init.control.estate init.control.reader init.lean.compiler.externattr init.lean.compiler.ir.basic init.lean.compiler.ir.compilerm init.lean.compiler.ir.freevars
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
obj* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_visitFnBody(obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_ExplicitBoxing_getResultType(obj*, obj*);
obj* l_Lean_IR_LocalContext_addLocal(obj*, obj*, uint8, obj*);
obj* l_Lean_IR_ExplicitBoxing_withJDecl(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(obj*, obj*);
obj* l_Lean_IR_explicitBoxing___boxed(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedName(obj*);
uint8 l_Lean_IR_Decl_resultType___main(obj*);
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
obj* l_Lean_IR_ExplicitBoxing_run(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(obj*);
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed(obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withVDecl(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_findEnvDecl_x27(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addJP(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(obj*);
namespace lean {
namespace ir {
obj* add_boxed_version_core(obj*, obj*);
}
}
uint8 l_Lean_isExtern(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkCast___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_ExplicitBoxing_getResultType___boxed(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(obj*);
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(obj*, uint8, obj*, uint8, obj*, obj*, obj*);
extern obj* l_Lean_IR_declMapExt;
uint8 l_Lean_IR_ExplicitBoxing_eqvTypes(uint8, uint8);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getVarType(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_paramInh;
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_getType(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_getJPParams(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getLocalContext(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkFresh(obj*);
obj* l_Lean_PersistentEnvExtension_addEntry___rarg(obj*, obj*, obj*);
uint8 l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
obj* l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
obj* l_Lean_IR_getEnv___rarg(obj*);
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_params___main(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getDecl(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(obj*);
obj* l_Lean_IR_ExplicitBoxing_getEnv(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getVarType___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getDecl___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_getJPParams(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_addBoxedVersions(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_boxing_1__mkFresh(obj*);
obj* l_Lean_IR_ExplicitBoxing_getEnv___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_ExplicitBoxing_getScrutineeType(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(uint8, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_visitFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withParams(obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_explicitBoxing(obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ExplicitBoxing_mkCast(obj*, uint8);
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isScalar___main(uint8);
obj* _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_boxed");
return x_1;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkBoxedName(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_boxing_1__mkFresh(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; uint8 x_9; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1 + 1);
x_9 = l_Lean_IR_IRType_isScalar___main(x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::dec(x_7);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean::dec(x_3);
return x_10;
}
}
else
{
lean::dec(x_7);
if (x_1 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean::dec(x_3);
return x_1;
}
}
}
}
}
uint8 l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = l_Lean_IR_Decl_params___main(x_2);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_lt(x_5, x_4);
lean::dec(x_4);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; uint8 x_9; 
x_8 = l_Lean_IR_Decl_resultType___main(x_2);
x_9 = l_Lean_IR_IRType_isScalar___main(x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_6, x_3, x_5);
lean::dec(x_3);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = l_Lean_IR_Decl_name___main(x_2);
x_12 = l_Lean_isExtern(x_1, x_11);
lean::dec(x_11);
return x_12;
}
else
{
return x_6;
}
}
else
{
lean::dec(x_3);
return x_6;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_5 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_4, x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_2;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_9 = lean::array_fget(x_2, x_1);
x_10 = lean::box(0);
lean::inc(x_9);
x_11 = x_10;
x_12 = lean::array_fset(x_2, x_1, x_11);
x_13 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_3);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
x_16 = 0;
x_17 = 7;
x_18 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*1 + 1, x_17);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_add(x_1, x_19);
x_21 = x_18;
x_22 = lean::array_fset(x_12, x_1, x_21);
lean::dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_4, x_9);
lean::dec(x_4);
x_11 = lean::nat_sub(x_3, x_10);
x_12 = lean::nat_sub(x_11, x_9);
lean::dec(x_11);
x_13 = !lean::is_exclusive(x_5);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; uint8 x_20; 
x_14 = lean::cnstr_get(x_5, 0);
x_15 = lean::cnstr_get(x_5, 1);
x_16 = l_Lean_IR_paramInh;
x_17 = lean::array_get(x_16, x_1, x_12);
x_18 = lean::array_get(x_16, x_2, x_12);
lean::dec(x_12);
x_19 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1 + 1);
lean::dec(x_17);
x_20 = l_Lean_IR_IRType_isScalar___main(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
lean::dec(x_18);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::array_push(x_15, x_22);
lean::cnstr_set(x_5, 1, x_23);
x_4 = x_10;
goto _start;
}
else
{
obj* x_25; uint8 x_26; 
lean::free_heap_obj(x_5);
x_25 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_6);
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
x_29 = lean::cnstr_get(x_18, 0);
lean::inc(x_29);
lean::dec(x_18);
x_30 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::box(13);
lean::inc(x_27);
x_32 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_19);
x_33 = lean::array_push(x_14, x_32);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_27);
x_35 = lean::array_push(x_15, x_34);
lean::cnstr_set(x_25, 1, x_35);
lean::cnstr_set(x_25, 0, x_33);
x_4 = x_10;
x_5 = x_25;
x_6 = x_28;
goto _start;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_37 = lean::cnstr_get(x_25, 0);
x_38 = lean::cnstr_get(x_25, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_25);
x_39 = lean::cnstr_get(x_18, 0);
lean::inc(x_39);
lean::dec(x_18);
x_40 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::box(13);
lean::inc(x_37);
x_42 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*3, x_19);
x_43 = lean::array_push(x_14, x_42);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_37);
x_45 = lean::array_push(x_15, x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
x_4 = x_10;
x_5 = x_46;
x_6 = x_38;
goto _start;
}
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; uint8 x_54; 
x_48 = lean::cnstr_get(x_5, 0);
x_49 = lean::cnstr_get(x_5, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_5);
x_50 = l_Lean_IR_paramInh;
x_51 = lean::array_get(x_50, x_1, x_12);
x_52 = lean::array_get(x_50, x_2, x_12);
lean::dec(x_12);
x_53 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1 + 1);
lean::dec(x_51);
x_54 = l_Lean_IR_IRType_isScalar___main(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
lean::dec(x_52);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::array_push(x_49, x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_48);
lean::cnstr_set(x_58, 1, x_57);
x_4 = x_10;
x_5 = x_58;
goto _start;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_60 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_6);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_60, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_63 = x_60;
} else {
 lean::dec_ref(x_60);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_52, 0);
lean::inc(x_64);
lean::dec(x_52);
x_65 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::box(13);
lean::inc(x_61);
x_67 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set(x_67, 2, x_66);
lean::cnstr_set_scalar(x_67, sizeof(void*)*3, x_53);
x_68 = lean::array_push(x_48, x_67);
x_69 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_69, 0, x_61);
x_70 = lean::array_push(x_49, x_69);
if (lean::is_scalar(x_63)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_63;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
x_4 = x_10;
x_5 = x_71;
x_6 = x_62;
goto _start;
}
}
}
else
{
obj* x_73; 
lean::dec(x_4);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_5);
lean::cnstr_set(x_73, 1, x_6);
return x_73;
}
}
}
obj* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
lean::inc(x_2);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_3 = l_Lean_IR_Decl_params___main(x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_3);
x_5 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(x_4, x_3, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::array_get_size(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean::inc(x_8);
x_10 = l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_3, x_6, x_8, x_8, x_9, x_7);
lean::dec(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_15 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_12);
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = lean::cnstr_get(x_15, 1);
x_19 = l_Lean_IR_Decl_resultType___main(x_1);
x_20 = l_Lean_IR_Decl_name___main(x_1);
lean::inc(x_20);
x_21 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
x_22 = lean::box(13);
lean::inc(x_17);
x_23 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set(x_23, 2, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*3, x_19);
x_24 = lean::array_push(x_13, x_23);
x_25 = l_Lean_IR_IRType_isScalar___main(x_19);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; uint8 x_31; obj* x_32; 
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_17);
x_27 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = l_Lean_IR_reshape(x_24, x_27);
x_29 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_30 = lean_name_mk_string(x_20, x_29);
x_31 = 7;
x_32 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_6);
lean::cnstr_set(x_32, 2, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_31);
lean::cnstr_set(x_15, 0, x_32);
return x_15;
}
else
{
obj* x_33; uint8 x_34; 
lean::free_heap_obj(x_15);
x_33 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_18);
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_33, 0);
x_36 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_36, 0, x_17);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_19);
x_37 = 7;
lean::inc(x_35);
x_38 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_36);
lean::cnstr_set(x_38, 2, x_22);
lean::cnstr_set_scalar(x_38, sizeof(void*)*3, x_37);
x_39 = lean::array_push(x_24, x_38);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_35);
x_41 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = l_Lean_IR_reshape(x_39, x_41);
x_43 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_44 = lean_name_mk_string(x_20, x_43);
x_45 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_6);
lean::cnstr_set(x_45, 2, x_42);
lean::cnstr_set_scalar(x_45, sizeof(void*)*3, x_37);
lean::cnstr_set(x_33, 0, x_45);
return x_33;
}
else
{
obj* x_46; obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_46 = lean::cnstr_get(x_33, 0);
x_47 = lean::cnstr_get(x_33, 1);
lean::inc(x_47);
lean::inc(x_46);
lean::dec(x_33);
x_48 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_48, 0, x_17);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_19);
x_49 = 7;
lean::inc(x_46);
x_50 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set(x_50, 1, x_48);
lean::cnstr_set(x_50, 2, x_22);
lean::cnstr_set_scalar(x_50, sizeof(void*)*3, x_49);
x_51 = lean::array_push(x_24, x_50);
x_52 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_52, 0, x_46);
x_53 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = l_Lean_IR_reshape(x_51, x_53);
x_55 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_56 = lean_name_mk_string(x_20, x_55);
x_57 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_6);
lean::cnstr_set(x_57, 2, x_54);
lean::cnstr_set_scalar(x_57, sizeof(void*)*3, x_49);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_47);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; uint8 x_67; 
x_59 = lean::cnstr_get(x_15, 0);
x_60 = lean::cnstr_get(x_15, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_15);
x_61 = l_Lean_IR_Decl_resultType___main(x_1);
x_62 = l_Lean_IR_Decl_name___main(x_1);
lean::inc(x_62);
x_63 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_14);
x_64 = lean::box(13);
lean::inc(x_59);
x_65 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_65, 0, x_59);
lean::cnstr_set(x_65, 1, x_63);
lean::cnstr_set(x_65, 2, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*3, x_61);
x_66 = lean::array_push(x_13, x_65);
x_67 = l_Lean_IR_IRType_isScalar___main(x_61);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; 
x_68 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_68, 0, x_59);
x_69 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = l_Lean_IR_reshape(x_66, x_69);
x_71 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_72 = lean_name_mk_string(x_62, x_71);
x_73 = 7;
x_74 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_6);
lean::cnstr_set(x_74, 2, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*3, x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_60);
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_76 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_60);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_76, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 lean::cnstr_release(x_76, 1);
 x_79 = x_76;
} else {
 lean::dec_ref(x_76);
 x_79 = lean::box(0);
}
x_80 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_80, 0, x_59);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_61);
x_81 = 7;
lean::inc(x_77);
x_82 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_82, 0, x_77);
lean::cnstr_set(x_82, 1, x_80);
lean::cnstr_set(x_82, 2, x_64);
lean::cnstr_set_scalar(x_82, sizeof(void*)*3, x_81);
x_83 = lean::array_push(x_66, x_82);
x_84 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_84, 0, x_77);
x_85 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = l_Lean_IR_reshape(x_83, x_85);
x_87 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_88 = lean_name_mk_string(x_62, x_87);
x_89 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_6);
lean::cnstr_set(x_89, 2, x_86);
lean::cnstr_set_scalar(x_89, sizeof(void*)*3, x_81);
if (lean::is_scalar(x_79)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_79;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_78);
return x_90;
}
}
}
}
obj* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
if (x_9 == 0)
{
lean::dec(x_8);
x_4 = x_11;
goto _start;
}
else
{
obj* x_13; obj* x_14; 
x_13 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_8);
lean::dec(x_8);
x_14 = lean::array_push(x_5, x_13);
x_4 = x_11;
x_5 = x_14;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_addBoxedVersions(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_2, x_3, x_4);
x_6 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_5, x_5, x_3, x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
namespace lean {
namespace ir {
obj* add_boxed_version_core(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_2);
if (x_3 == 0)
{
lean::dec(x_2);
return x_1;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_2);
lean::dec(x_2);
x_5 = l_Lean_IR_declMapExt;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
}
}
}
uint8 l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 0;
return x_5;
}
else
{
obj* x_6; 
x_6 = lean::array_fget(x_1, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = l_Lean_IR_CtorInfo_isScalar(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = 1;
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
x_2 = x_11;
goto _start;
}
}
else
{
uint8 x_13; 
lean::dec(x_6);
lean::dec(x_2);
x_13 = 1;
return x_13;
}
}
}
}
uint8 l_Lean_IR_ExplicitBoxing_getScrutineeType(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 7;
return x_5;
}
else
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(256u);
x_9 = lean::nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(65536u);
x_11 = lean::nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::mk_nat_obj(lean::mpz("4294967296"));
x_13 = lean::nat_dec_lt(x_2, x_12);
lean::dec(x_2);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = 7;
return x_14;
}
else
{
uint8 x_15; 
x_15 = 3;
return x_15;
}
}
else
{
uint8 x_16; 
lean::dec(x_2);
x_16 = 2;
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_2);
x_17 = 1;
return x_17;
}
}
else
{
uint8 x_18; 
lean::dec(x_2);
x_18 = 7;
return x_18;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_IR_ExplicitBoxing_eqvTypes(uint8 x_1, uint8 x_2) {
_start:
{
uint8 x_3; uint8 x_4; 
x_3 = l_Lean_IR_IRType_isScalar___main(x_1);
x_4 = l_Lean_IR_IRType_isScalar___main(x_2);
if (x_3 == 0)
{
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (x_4 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = l_Lean_IR_IRType_beq___main(x_1, x_2);
return x_8;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_mkFresh___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_mkFresh(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_getEnv(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_getEnv___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getEnv(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getLocalContext(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getResultType(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_4 = lean::box(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_getResultType___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getResultType(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_ExplicitBoxing_getVarType(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getType(x_6, x_1);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; obj* x_9; 
x_8 = 7;
x_9 = lean::box(x_8);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_10);
return x_4;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_4, 0);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_4);
x_13 = l_Lean_IR_LocalContext_getType(x_11, x_1);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; obj* x_15; obj* x_16; 
x_14 = 7;
x_15 = lean::box(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_12);
return x_18;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_getVarType___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_getJPParams(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getJPParams(x_6, x_1);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
x_8 = l_Array_empty___closed__1;
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_4);
x_12 = l_Lean_IR_LocalContext_getJPParams(x_10, x_1);
lean::dec(x_10);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_Array_empty___closed__1;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getJPParams(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
x_3 = lean::box(0);
x_4 = 6;
x_5 = lean::box(13);
x_6 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*3, x_4);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_getDecl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 2);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_getDecl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getDecl(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_7, x_6);
lean::cnstr_set(x_3, 0, x_8);
x_9 = lean::apply_2(x_2, x_3, x_4);
return x_9;
}
else
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_12 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_10);
lean::dec(x_3);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_14, x_10);
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_13);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_11);
x_17 = lean::apply_2(x_2, x_16, x_4);
return x_17;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_withParams___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_5, 0);
x_9 = l_Lean_IR_LocalContext_addLocal(x_8, x_1, x_2, x_3);
lean::cnstr_set(x_5, 0, x_9);
x_10 = lean::apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*3);
x_13 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_11);
lean::dec(x_5);
x_15 = l_Lean_IR_LocalContext_addLocal(x_11, x_1, x_2, x_3);
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_12);
x_17 = lean::apply_2(x_4, x_16, x_6);
return x_17;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_withVDecl___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_5, 0);
x_9 = l_Lean_IR_LocalContext_addJP(x_8, x_1, x_2, x_3);
lean::cnstr_set(x_5, 0, x_9);
x_10 = lean::apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*3);
x_13 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_11);
lean::dec(x_5);
x_15 = l_Lean_IR_LocalContext_addJP(x_11, x_1, x_2, x_3);
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_12);
x_17 = lean::apply_2(x_4, x_16, x_6);
return x_17;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_withJDecl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_ExplicitBoxing_withJDecl___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_IR_ExplicitBoxing_mkCast(obj* x_1, uint8 x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_IRType_isScalar___main(x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_4, 0, x_1);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::alloc_cnstr(9, 1, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*1, x_2);
return x_5;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_mkCast___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_3);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; uint8 x_10; 
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::unbox(x_7);
x_10 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_9, x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_11 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_8);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::unbox(x_7);
lean::dec(x_7);
x_15 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_14);
lean::inc(x_12);
x_16 = lean::apply_3(x_3, x_12, x_4, x_13);
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set(x_19, 2, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*3, x_2);
lean::cnstr_set(x_16, 0, x_19);
return x_16;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_16, 0);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*3, x_2);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
}
else
{
obj* x_24; 
lean::dec(x_7);
x_24 = lean::apply_3(x_3, x_1, x_4, x_8);
return x_24;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_castVarIfNeeded(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; uint8 x_12; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = l_Lean_IR_ExplicitBoxing_getVarType(x_7, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
lean::dec(x_8);
x_11 = lean::unbox(x_9);
x_12 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_11, x_2);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_13 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_10);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::unbox(x_9);
lean::dec(x_9);
x_17 = l_Lean_IR_ExplicitBoxing_mkCast(x_7, x_16);
lean::inc(x_14);
lean::cnstr_set(x_1, 0, x_14);
x_18 = lean::apply_3(x_3, x_1, x_4, x_15);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_2);
lean::cnstr_set(x_18, 0, x_21);
return x_18;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_18, 0);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_18);
x_24 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_24, 0, x_14);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*3, x_2);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
}
else
{
obj* x_26; 
lean::dec(x_9);
x_26 = lean::apply_3(x_3, x_1, x_4, x_10);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; uint8 x_31; uint8 x_32; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
lean::dec(x_1);
x_28 = l_Lean_IR_ExplicitBoxing_getVarType(x_27, x_4, x_5);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_31 = lean::unbox(x_29);
x_32 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_31, x_2);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_33 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_30);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
lean::dec(x_33);
x_36 = lean::unbox(x_29);
lean::dec(x_29);
x_37 = l_Lean_IR_ExplicitBoxing_mkCast(x_27, x_36);
lean::inc(x_34);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_34);
x_39 = lean::apply_3(x_3, x_38, x_4, x_35);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_39, 1);
lean::inc(x_41);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_42 = x_39;
} else {
 lean::dec_ref(x_39);
 x_42 = lean::box(0);
}
x_43 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_43, 0, x_34);
lean::cnstr_set(x_43, 1, x_37);
lean::cnstr_set(x_43, 2, x_40);
lean::cnstr_set_scalar(x_43, sizeof(void*)*3, x_2);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_29);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_27);
x_46 = lean::apply_3(x_3, x_45, x_4, x_30);
return x_46;
}
}
}
else
{
obj* x_47; 
x_47 = lean::apply_3(x_3, x_1, x_4, x_5);
return x_47;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_3);
x_9 = lean::nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_11 = lean::array_fget(x_3, x_4);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
lean::inc(x_2);
x_14 = lean::apply_1(x_2, x_4);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_5, 1);
lean::inc(x_17);
lean::dec(x_5);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
x_19 = l_Lean_IR_ExplicitBoxing_getVarType(x_18, x_6, x_7);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; uint8 x_23; uint8 x_24; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
x_23 = lean::unbox(x_21);
x_24 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_23, x_15);
if (x_24 == 0)
{
uint8 x_25; 
lean::free_heap_obj(x_19);
x_25 = !lean::is_exclusive(x_11);
if (x_25 == 0)
{
obj* x_26; obj* x_27; uint8 x_28; 
x_26 = lean::cnstr_get(x_11, 0);
lean::dec(x_26);
x_27 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
x_31 = lean::unbox(x_21);
lean::dec(x_21);
x_32 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_31);
x_33 = lean::box(13);
lean::inc(x_29);
x_34 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_32);
lean::cnstr_set(x_34, 2, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*3, x_15);
lean::cnstr_set(x_11, 0, x_29);
x_35 = lean::array_push(x_16, x_11);
x_36 = lean::array_push(x_17, x_34);
lean::cnstr_set(x_27, 1, x_36);
lean::cnstr_set(x_27, 0, x_35);
x_4 = x_13;
x_5 = x_27;
x_7 = x_30;
goto _start;
}
else
{
obj* x_38; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_38 = lean::cnstr_get(x_27, 0);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_27);
x_40 = lean::unbox(x_21);
lean::dec(x_21);
x_41 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_40);
x_42 = lean::box(13);
lean::inc(x_38);
x_43 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_43, 0, x_38);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set(x_43, 2, x_42);
lean::cnstr_set_scalar(x_43, sizeof(void*)*3, x_15);
lean::cnstr_set(x_11, 0, x_38);
x_44 = lean::array_push(x_16, x_11);
x_45 = lean::array_push(x_17, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
x_4 = x_13;
x_5 = x_46;
x_7 = x_39;
goto _start;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_51 = x_48;
} else {
 lean::dec_ref(x_48);
 x_51 = lean::box(0);
}
x_52 = lean::unbox(x_21);
lean::dec(x_21);
x_53 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_52);
x_54 = lean::box(13);
lean::inc(x_49);
x_55 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_55, 0, x_49);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*3, x_15);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_49);
x_57 = lean::array_push(x_16, x_56);
x_58 = lean::array_push(x_17, x_55);
if (lean::is_scalar(x_51)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_51;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
x_4 = x_13;
x_5 = x_59;
x_7 = x_50;
goto _start;
}
}
else
{
obj* x_61; 
lean::dec(x_21);
lean::dec(x_18);
x_61 = lean::array_push(x_16, x_11);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 0, x_61);
x_4 = x_13;
x_5 = x_19;
x_7 = x_22;
goto _start;
}
}
else
{
obj* x_63; obj* x_64; uint8 x_65; uint8 x_66; 
x_63 = lean::cnstr_get(x_19, 0);
x_64 = lean::cnstr_get(x_19, 1);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_19);
x_65 = lean::unbox(x_63);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_65, x_15);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_67 = x_11;
} else {
 lean::dec_ref(x_11);
 x_67 = lean::box(0);
}
x_68 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_64);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_68, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_71 = x_68;
} else {
 lean::dec_ref(x_68);
 x_71 = lean::box(0);
}
x_72 = lean::unbox(x_63);
lean::dec(x_63);
x_73 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_72);
x_74 = lean::box(13);
lean::inc(x_69);
x_75 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_75, 0, x_69);
lean::cnstr_set(x_75, 1, x_73);
lean::cnstr_set(x_75, 2, x_74);
lean::cnstr_set_scalar(x_75, sizeof(void*)*3, x_15);
if (lean::is_scalar(x_67)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_67;
}
lean::cnstr_set(x_76, 0, x_69);
x_77 = lean::array_push(x_16, x_76);
x_78 = lean::array_push(x_17, x_75);
if (lean::is_scalar(x_71)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_71;
}
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
x_4 = x_13;
x_5 = x_79;
x_7 = x_70;
goto _start;
}
else
{
obj* x_81; obj* x_82; 
lean::dec(x_63);
lean::dec(x_18);
x_81 = lean::array_push(x_16, x_11);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_17);
x_4 = x_13;
x_5 = x_82;
x_7 = x_64;
goto _start;
}
}
}
else
{
uint8 x_84; 
x_84 = !lean::is_exclusive(x_5);
if (x_84 == 0)
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_5, 0);
x_86 = lean::array_push(x_85, x_11);
lean::cnstr_set(x_5, 0, x_86);
x_4 = x_13;
goto _start;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get(x_5, 0);
x_89 = lean::cnstr_get(x_5, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_5);
x_90 = lean::array_push(x_88, x_11);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_4 = x_13;
x_5 = x_91;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_1, x_2, x_1, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_3);
x_9 = lean::nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::array_fget(x_3, x_4);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean::array_get(x_14, x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1 + 1);
lean::dec(x_15);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8 x_26; 
lean::free_heap_obj(x_20);
x_26 = !lean::is_exclusive(x_11);
if (x_26 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_11, 0);
lean::dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = lean::cnstr_get(x_28, 1);
x_32 = lean::unbox(x_22);
lean::dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean::box(13);
lean::inc(x_30);
x_35 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_30);
x_36 = lean::array_push(x_17, x_11);
x_37 = lean::array_push(x_18, x_35);
lean::cnstr_set(x_28, 1, x_37);
lean::cnstr_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_28, 0);
x_40 = lean::cnstr_get(x_28, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_28);
x_41 = lean::unbox(x_22);
lean::dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean::box(13);
lean::inc(x_39);
x_44 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
lean::cnstr_set_scalar(x_44, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_39);
x_45 = lean::array_push(x_17, x_11);
x_46 = lean::array_push(x_18, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = lean::unbox(x_22);
lean::dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean::box(13);
lean::inc(x_50);
x_56 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_54);
lean::cnstr_set(x_56, 2, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*3, x_16);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_50);
x_58 = lean::array_push(x_17, x_57);
x_59 = lean::array_push(x_18, x_56);
if (lean::is_scalar(x_52)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_52;
}
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
obj* x_62; 
lean::dec(x_22);
lean::dec(x_19);
x_62 = lean::array_push(x_17, x_11);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
obj* x_64; obj* x_65; uint8 x_66; uint8 x_67; 
x_64 = lean::cnstr_get(x_20, 0);
x_65 = lean::cnstr_get(x_20, 1);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_20);
x_66 = lean::unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_68 = x_11;
} else {
 lean::dec_ref(x_11);
 x_68 = lean::box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
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
x_73 = lean::unbox(x_64);
lean::dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean::box(13);
lean::inc(x_70);
x_76 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_76, 0, x_70);
lean::cnstr_set(x_76, 1, x_74);
lean::cnstr_set(x_76, 2, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*3, x_16);
if (lean::is_scalar(x_68)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_68;
}
lean::cnstr_set(x_77, 0, x_70);
x_78 = lean::array_push(x_17, x_77);
x_79 = lean::array_push(x_18, x_76);
if (lean::is_scalar(x_72)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_72;
}
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
obj* x_82; obj* x_83; 
lean::dec(x_64);
lean::dec(x_19);
x_82 = lean::array_push(x_17, x_11);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8 x_85; 
lean::dec(x_15);
x_85 = !lean::is_exclusive(x_5);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_5, 0);
x_87 = lean::array_push(x_86, x_11);
lean::cnstr_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_5, 0);
x_90 = lean::cnstr_get(x_5, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_5);
x_91 = lean::array_push(x_89, x_11);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_2, x_1, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_11 = lean::apply_3(x_3, x_9, x_4, x_8);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = l_Lean_IR_reshape(x_10, x_13);
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
x_17 = l_Lean_IR_reshape(x_10, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_2, x_3);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_4, 1);
lean::inc(x_14);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_16 = l_Lean_IR_ExplicitBoxing_getVarType(x_15, x_5, x_6);
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; uint8 x_20; uint8 x_21; uint8 x_22; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::cnstr_get(x_16, 1);
x_20 = 7;
x_21 = lean::unbox(x_18);
x_22 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_21, x_20);
if (x_22 == 0)
{
uint8 x_23; 
lean::free_heap_obj(x_16);
x_23 = !lean::is_exclusive(x_10);
if (x_23 == 0)
{
obj* x_24; obj* x_25; uint8 x_26; 
x_24 = lean::cnstr_get(x_10, 0);
lean::dec(x_24);
x_25 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
x_29 = lean::unbox(x_18);
lean::dec(x_18);
x_30 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_29);
x_31 = lean::box(13);
lean::inc(x_27);
x_32 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_32, 0, x_27);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*3, x_20);
lean::cnstr_set(x_10, 0, x_27);
x_33 = lean::array_push(x_13, x_10);
x_34 = lean::array_push(x_14, x_32);
lean::cnstr_set(x_25, 1, x_34);
lean::cnstr_set(x_25, 0, x_33);
x_3 = x_12;
x_4 = x_25;
x_6 = x_28;
goto _start;
}
else
{
obj* x_36; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_25, 0);
x_37 = lean::cnstr_get(x_25, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_25);
x_38 = lean::unbox(x_18);
lean::dec(x_18);
x_39 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_38);
x_40 = lean::box(13);
lean::inc(x_36);
x_41 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set(x_41, 1, x_39);
lean::cnstr_set(x_41, 2, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*3, x_20);
lean::cnstr_set(x_10, 0, x_36);
x_42 = lean::array_push(x_13, x_10);
x_43 = lean::array_push(x_14, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
x_3 = x_12;
x_4 = x_44;
x_6 = x_37;
goto _start;
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_10);
x_46 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_49 = x_46;
} else {
 lean::dec_ref(x_46);
 x_49 = lean::box(0);
}
x_50 = lean::unbox(x_18);
lean::dec(x_18);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_50);
x_52 = lean::box(13);
lean::inc(x_47);
x_53 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_53, 0, x_47);
lean::cnstr_set(x_53, 1, x_51);
lean::cnstr_set(x_53, 2, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*3, x_20);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_47);
x_55 = lean::array_push(x_13, x_54);
x_56 = lean::array_push(x_14, x_53);
if (lean::is_scalar(x_49)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_49;
}
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
x_3 = x_12;
x_4 = x_57;
x_6 = x_48;
goto _start;
}
}
else
{
obj* x_59; 
lean::dec(x_18);
lean::dec(x_15);
x_59 = lean::array_push(x_13, x_10);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set(x_16, 0, x_59);
x_3 = x_12;
x_4 = x_16;
x_6 = x_19;
goto _start;
}
}
else
{
obj* x_61; obj* x_62; uint8 x_63; uint8 x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_16, 0);
x_62 = lean::cnstr_get(x_16, 1);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_16);
x_63 = 7;
x_64 = lean::unbox(x_61);
x_65 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_63);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_66 = x_10;
} else {
 lean::dec_ref(x_10);
 x_66 = lean::box(0);
}
x_67 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_62);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_70 = x_67;
} else {
 lean::dec_ref(x_67);
 x_70 = lean::box(0);
}
x_71 = lean::unbox(x_61);
lean::dec(x_61);
x_72 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_71);
x_73 = lean::box(13);
lean::inc(x_68);
x_74 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_74, 0, x_68);
lean::cnstr_set(x_74, 1, x_72);
lean::cnstr_set(x_74, 2, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*3, x_63);
if (lean::is_scalar(x_66)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_66;
}
lean::cnstr_set(x_75, 0, x_68);
x_76 = lean::array_push(x_13, x_75);
x_77 = lean::array_push(x_14, x_74);
if (lean::is_scalar(x_70)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_70;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
x_3 = x_12;
x_4 = x_78;
x_6 = x_69;
goto _start;
}
else
{
obj* x_80; obj* x_81; 
lean::dec(x_61);
lean::dec(x_15);
x_80 = lean::array_push(x_13, x_10);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_14);
x_3 = x_12;
x_4 = x_81;
x_6 = x_62;
goto _start;
}
}
}
else
{
uint8 x_83; 
x_83 = !lean::is_exclusive(x_4);
if (x_83 == 0)
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_4, 0);
x_85 = lean::array_push(x_84, x_10);
lean::cnstr_set(x_4, 0, x_85);
x_3 = x_12;
goto _start;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_87 = lean::cnstr_get(x_4, 0);
x_88 = lean::cnstr_get(x_4, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_4);
x_89 = lean::array_push(x_87, x_10);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
x_3 = x_12;
x_4 = x_90;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_1, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::apply_3(x_2, x_8, x_3, x_7);
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_IR_reshape(x_9, x_12);
lean::cnstr_set(x_10, 0, x_13);
return x_10;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_10);
x_16 = l_Lean_IR_reshape(x_9, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
return x_17;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_Lean_IR_IRType_isScalar___main(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_4);
lean::cnstr_set_scalar(x_8, sizeof(void*)*3, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
else
{
obj* x_10; uint8 x_11; 
x_10 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_6);
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_13 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_4);
lean::cnstr_set_scalar(x_14, sizeof(void*)*3, x_2);
x_15 = 7;
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_15);
lean::cnstr_set(x_10, 0, x_16);
return x_10;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_10, 0);
x_18 = lean::cnstr_get(x_10, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_10);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_19, 0, x_17);
x_20 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_4);
lean::cnstr_set_scalar(x_20, sizeof(void*)*3, x_2);
x_21 = 7;
x_22 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_3);
lean::cnstr_set(x_22, 2, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*3, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_18);
return x_23;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_7, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(obj* x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_4);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_7);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_12 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_4);
x_13 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_5);
lean::cnstr_set_scalar(x_13, sizeof(void*)*3, x_2);
x_14 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_3);
lean::cnstr_set(x_14, 2, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*3, x_4);
lean::cnstr_set(x_9, 0, x_14);
return x_9;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_9);
lean::inc(x_15);
x_17 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_4);
x_18 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_5);
lean::cnstr_set_scalar(x_18, sizeof(void*)*3, x_2);
x_19 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set(x_19, 2, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*3, x_4);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_5);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_2);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
return x_22;
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; obj* x_10; 
x_8 = lean::unbox(x_2);
lean::dec(x_2);
x_9 = lean::unbox(x_4);
lean::dec(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_8, x_3, x_9, x_5, x_6, x_7);
lean::dec(x_6);
return x_10;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_3);
x_9 = lean::nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::array_fget(x_3, x_4);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean::array_get(x_14, x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1 + 1);
lean::dec(x_15);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8 x_26; 
lean::free_heap_obj(x_20);
x_26 = !lean::is_exclusive(x_11);
if (x_26 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_11, 0);
lean::dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = lean::cnstr_get(x_28, 1);
x_32 = lean::unbox(x_22);
lean::dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean::box(13);
lean::inc(x_30);
x_35 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_30);
x_36 = lean::array_push(x_17, x_11);
x_37 = lean::array_push(x_18, x_35);
lean::cnstr_set(x_28, 1, x_37);
lean::cnstr_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_28, 0);
x_40 = lean::cnstr_get(x_28, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_28);
x_41 = lean::unbox(x_22);
lean::dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean::box(13);
lean::inc(x_39);
x_44 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
lean::cnstr_set_scalar(x_44, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_39);
x_45 = lean::array_push(x_17, x_11);
x_46 = lean::array_push(x_18, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = lean::unbox(x_22);
lean::dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean::box(13);
lean::inc(x_50);
x_56 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_54);
lean::cnstr_set(x_56, 2, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*3, x_16);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_50);
x_58 = lean::array_push(x_17, x_57);
x_59 = lean::array_push(x_18, x_56);
if (lean::is_scalar(x_52)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_52;
}
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
obj* x_62; 
lean::dec(x_22);
lean::dec(x_19);
x_62 = lean::array_push(x_17, x_11);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
obj* x_64; obj* x_65; uint8 x_66; uint8 x_67; 
x_64 = lean::cnstr_get(x_20, 0);
x_65 = lean::cnstr_get(x_20, 1);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_20);
x_66 = lean::unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_68 = x_11;
} else {
 lean::dec_ref(x_11);
 x_68 = lean::box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
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
x_73 = lean::unbox(x_64);
lean::dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean::box(13);
lean::inc(x_70);
x_76 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_76, 0, x_70);
lean::cnstr_set(x_76, 1, x_74);
lean::cnstr_set(x_76, 2, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*3, x_16);
if (lean::is_scalar(x_68)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_68;
}
lean::cnstr_set(x_77, 0, x_70);
x_78 = lean::array_push(x_17, x_77);
x_79 = lean::array_push(x_18, x_76);
if (lean::is_scalar(x_72)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_72;
}
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
obj* x_82; obj* x_83; 
lean::dec(x_64);
lean::dec(x_19);
x_82 = lean::array_push(x_17, x_11);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8 x_85; 
lean::dec(x_15);
x_85 = !lean::is_exclusive(x_5);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_5, 0);
x_87 = lean::array_push(x_86, x_11);
lean::cnstr_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_5, 0);
x_90 = lean::cnstr_get(x_5, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_5);
x_91 = lean::array_push(x_89, x_11);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
x_10 = l_Lean_IR_CtorInfo_isScalar(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_11 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean::dec(x_9);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
lean::cnstr_set(x_3, 1, x_15);
x_17 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_3);
lean::cnstr_set(x_17, 2, x_4);
lean::cnstr_set_scalar(x_17, sizeof(void*)*3, x_2);
x_18 = l_Lean_IR_reshape(x_16, x_17);
lean::cnstr_set(x_12, 1, x_13);
lean::cnstr_set(x_12, 0, x_18);
return x_12;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_12, 0);
x_20 = lean::cnstr_get(x_12, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_12);
lean::cnstr_set(x_3, 1, x_19);
x_21 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_4);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_2);
x_22 = l_Lean_IR_reshape(x_20, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_13);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = l_Lean_IR_IRType_isScalar___main(x_2);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; uint8 x_28; 
x_25 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean::dec(x_9);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_28 = !lean::is_exclusive(x_26);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
lean::cnstr_set(x_3, 1, x_29);
x_31 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_3);
lean::cnstr_set(x_31, 2, x_4);
lean::cnstr_set_scalar(x_31, sizeof(void*)*3, x_2);
x_32 = l_Lean_IR_reshape(x_30, x_31);
lean::cnstr_set(x_26, 1, x_27);
lean::cnstr_set(x_26, 0, x_32);
return x_26;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_26, 0);
x_34 = lean::cnstr_get(x_26, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_26);
lean::cnstr_set(x_3, 1, x_33);
x_35 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_4);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_2);
x_36 = l_Lean_IR_reshape(x_34, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_27);
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::free_heap_obj(x_3);
lean::dec(x_9);
x_38 = lean::cnstr_get(x_8, 1);
lean::inc(x_38);
lean::dec(x_8);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set(x_41, 2, x_4);
lean::cnstr_set_scalar(x_41, sizeof(void*)*3, x_2);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_6);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; uint8 x_45; 
x_43 = lean::cnstr_get(x_3, 0);
x_44 = lean::cnstr_get(x_3, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_3);
x_45 = l_Lean_IR_CtorInfo_isScalar(x_43);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_46 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_44, x_5, x_6);
lean::dec(x_44);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
lean::dec(x_46);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_51 = x_47;
} else {
 lean::dec_ref(x_47);
 x_51 = lean::box(0);
}
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_43);
lean::cnstr_set(x_52, 1, x_49);
x_53 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set(x_53, 2, x_4);
lean::cnstr_set_scalar(x_53, sizeof(void*)*3, x_2);
x_54 = l_Lean_IR_reshape(x_50, x_53);
if (lean::is_scalar(x_51)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_51;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
return x_55;
}
else
{
uint8 x_56; 
x_56 = l_Lean_IR_IRType_isScalar___main(x_2);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_57 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_44, x_5, x_6);
lean::dec(x_44);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
lean::dec(x_57);
x_60 = lean::cnstr_get(x_58, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_62 = x_58;
} else {
 lean::dec_ref(x_58);
 x_62 = lean::box(0);
}
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_43);
lean::cnstr_set(x_63, 1, x_60);
x_64 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_64, 0, x_1);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set(x_64, 2, x_4);
lean::cnstr_set_scalar(x_64, sizeof(void*)*3, x_2);
x_65 = l_Lean_IR_reshape(x_61, x_64);
if (lean::is_scalar(x_62)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_62;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_59);
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_44);
x_67 = lean::cnstr_get(x_43, 1);
lean::inc(x_67);
lean::dec(x_43);
x_68 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_70, 0, x_1);
lean::cnstr_set(x_70, 1, x_69);
lean::cnstr_set(x_70, 2, x_4);
lean::cnstr_set_scalar(x_70, sizeof(void*)*3, x_2);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_6);
return x_71;
}
}
}
}
case 2:
{
uint8 x_72; 
x_72 = !lean::is_exclusive(x_3);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; uint8 x_77; 
x_73 = lean::cnstr_get(x_3, 2);
x_74 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_73, x_5, x_6);
lean::dec(x_73);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_74, 1);
lean::inc(x_76);
lean::dec(x_74);
x_77 = !lean::is_exclusive(x_75);
if (x_77 == 0)
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_78 = lean::cnstr_get(x_75, 0);
x_79 = lean::cnstr_get(x_75, 1);
lean::cnstr_set(x_3, 2, x_78);
x_80 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_80, 0, x_1);
lean::cnstr_set(x_80, 1, x_3);
lean::cnstr_set(x_80, 2, x_4);
lean::cnstr_set_scalar(x_80, sizeof(void*)*3, x_2);
x_81 = l_Lean_IR_reshape(x_79, x_80);
lean::cnstr_set(x_75, 1, x_76);
lean::cnstr_set(x_75, 0, x_81);
return x_75;
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_75, 0);
x_83 = lean::cnstr_get(x_75, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_75);
lean::cnstr_set(x_3, 2, x_82);
x_84 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_84, 0, x_1);
lean::cnstr_set(x_84, 1, x_3);
lean::cnstr_set(x_84, 2, x_4);
lean::cnstr_set_scalar(x_84, sizeof(void*)*3, x_2);
x_85 = l_Lean_IR_reshape(x_83, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_76);
return x_86;
}
}
else
{
obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_87 = lean::cnstr_get(x_3, 0);
x_88 = lean::cnstr_get(x_3, 1);
x_89 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_90 = lean::cnstr_get(x_3, 2);
lean::inc(x_90);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_3);
x_91 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_90, x_5, x_6);
lean::dec(x_90);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
lean::dec(x_91);
x_94 = lean::cnstr_get(x_92, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_96 = x_92;
} else {
 lean::dec_ref(x_92);
 x_96 = lean::box(0);
}
x_97 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_97, 0, x_87);
lean::cnstr_set(x_97, 1, x_88);
lean::cnstr_set(x_97, 2, x_94);
lean::cnstr_set_scalar(x_97, sizeof(void*)*3, x_89);
x_98 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_98, 0, x_1);
lean::cnstr_set(x_98, 1, x_97);
lean::cnstr_set(x_98, 2, x_4);
lean::cnstr_set_scalar(x_98, sizeof(void*)*3, x_2);
x_99 = l_Lean_IR_reshape(x_95, x_98);
if (lean::is_scalar(x_96)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_96;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_93);
return x_100;
}
}
case 6:
{
uint8 x_101; 
x_101 = !lean::is_exclusive(x_3);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; uint8 x_113; obj* x_114; uint8 x_115; 
x_102 = lean::cnstr_get(x_3, 0);
x_103 = lean::cnstr_get(x_3, 1);
x_104 = l_Lean_IR_ExplicitBoxing_getDecl(x_102, x_5, x_6);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_104, 1);
lean::inc(x_106);
lean::dec(x_104);
x_107 = l_Lean_IR_Decl_params___main(x_105);
x_108 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_107, x_103, x_5, x_106);
lean::dec(x_103);
lean::dec(x_107);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_108, 1);
lean::inc(x_110);
lean::dec(x_108);
x_111 = lean::cnstr_get(x_109, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
lean::cnstr_set(x_3, 1, x_111);
x_113 = l_Lean_IR_Decl_resultType___main(x_105);
lean::dec(x_105);
x_114 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_113, x_4, x_5, x_110);
x_115 = !lean::is_exclusive(x_114);
if (x_115 == 0)
{
obj* x_116; obj* x_117; 
x_116 = lean::cnstr_get(x_114, 0);
x_117 = l_Lean_IR_reshape(x_112, x_116);
lean::cnstr_set(x_114, 0, x_117);
return x_114;
}
else
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_118 = lean::cnstr_get(x_114, 0);
x_119 = lean::cnstr_get(x_114, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_114);
x_120 = l_Lean_IR_reshape(x_112, x_118);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_119);
return x_121;
}
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; uint8 x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_122 = lean::cnstr_get(x_3, 0);
x_123 = lean::cnstr_get(x_3, 1);
lean::inc(x_123);
lean::inc(x_122);
lean::dec(x_3);
x_124 = l_Lean_IR_ExplicitBoxing_getDecl(x_122, x_5, x_6);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_124, 1);
lean::inc(x_126);
lean::dec(x_124);
x_127 = l_Lean_IR_Decl_params___main(x_125);
x_128 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_127, x_123, x_5, x_126);
lean::dec(x_123);
lean::dec(x_127);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_128, 1);
lean::inc(x_130);
lean::dec(x_128);
x_131 = lean::cnstr_get(x_129, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
lean::dec(x_129);
x_133 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_133, 0, x_122);
lean::cnstr_set(x_133, 1, x_131);
x_134 = l_Lean_IR_Decl_resultType___main(x_125);
lean::dec(x_125);
x_135 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_133, x_134, x_4, x_5, x_130);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_135, 1);
lean::inc(x_137);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_138 = x_135;
} else {
 lean::dec_ref(x_135);
 x_138 = lean::box(0);
}
x_139 = l_Lean_IR_reshape(x_132, x_136);
if (lean::is_scalar(x_138)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_138;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_137);
return x_140;
}
}
case 7:
{
uint8 x_141; 
x_141 = !lean::is_exclusive(x_3);
if (x_141 == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; uint8 x_150; obj* x_151; 
x_142 = lean::cnstr_get(x_3, 0);
x_143 = lean::cnstr_get(x_3, 1);
x_144 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_144, 1);
lean::inc(x_146);
lean::dec(x_144);
x_147 = l_Lean_IR_ExplicitBoxing_getDecl(x_142, x_5, x_146);
x_148 = lean::cnstr_get(x_147, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_147, 1);
lean::inc(x_149);
lean::dec(x_147);
x_150 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_145, x_148);
lean::dec(x_148);
lean::dec(x_145);
x_151 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_143, x_5, x_149);
lean::dec(x_143);
if (x_150 == 0)
{
obj* x_152; obj* x_153; uint8 x_154; 
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_153 = lean::cnstr_get(x_151, 1);
lean::inc(x_153);
lean::dec(x_151);
x_154 = !lean::is_exclusive(x_152);
if (x_154 == 0)
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_155 = lean::cnstr_get(x_152, 0);
x_156 = lean::cnstr_get(x_152, 1);
lean::cnstr_set(x_3, 1, x_155);
x_157 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_157, 0, x_1);
lean::cnstr_set(x_157, 1, x_3);
lean::cnstr_set(x_157, 2, x_4);
lean::cnstr_set_scalar(x_157, sizeof(void*)*3, x_2);
x_158 = l_Lean_IR_reshape(x_156, x_157);
lean::cnstr_set(x_152, 1, x_153);
lean::cnstr_set(x_152, 0, x_158);
return x_152;
}
else
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_159 = lean::cnstr_get(x_152, 0);
x_160 = lean::cnstr_get(x_152, 1);
lean::inc(x_160);
lean::inc(x_159);
lean::dec(x_152);
lean::cnstr_set(x_3, 1, x_159);
x_161 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_161, 0, x_1);
lean::cnstr_set(x_161, 1, x_3);
lean::cnstr_set(x_161, 2, x_4);
lean::cnstr_set_scalar(x_161, sizeof(void*)*3, x_2);
x_162 = l_Lean_IR_reshape(x_160, x_161);
x_163 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_153);
return x_163;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; uint8 x_168; 
x_164 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_165 = lean_name_mk_string(x_142, x_164);
x_166 = lean::cnstr_get(x_151, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_151, 1);
lean::inc(x_167);
lean::dec(x_151);
x_168 = !lean::is_exclusive(x_166);
if (x_168 == 0)
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
x_169 = lean::cnstr_get(x_166, 0);
x_170 = lean::cnstr_get(x_166, 1);
lean::cnstr_set(x_3, 1, x_169);
lean::cnstr_set(x_3, 0, x_165);
x_171 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_171, 0, x_1);
lean::cnstr_set(x_171, 1, x_3);
lean::cnstr_set(x_171, 2, x_4);
lean::cnstr_set_scalar(x_171, sizeof(void*)*3, x_2);
x_172 = l_Lean_IR_reshape(x_170, x_171);
lean::cnstr_set(x_166, 1, x_167);
lean::cnstr_set(x_166, 0, x_172);
return x_166;
}
else
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_173 = lean::cnstr_get(x_166, 0);
x_174 = lean::cnstr_get(x_166, 1);
lean::inc(x_174);
lean::inc(x_173);
lean::dec(x_166);
lean::cnstr_set(x_3, 1, x_173);
lean::cnstr_set(x_3, 0, x_165);
x_175 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_175, 0, x_1);
lean::cnstr_set(x_175, 1, x_3);
lean::cnstr_set(x_175, 2, x_4);
lean::cnstr_set_scalar(x_175, sizeof(void*)*3, x_2);
x_176 = l_Lean_IR_reshape(x_174, x_175);
x_177 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_167);
return x_177;
}
}
}
else
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; uint8 x_186; obj* x_187; 
x_178 = lean::cnstr_get(x_3, 0);
x_179 = lean::cnstr_get(x_3, 1);
lean::inc(x_179);
lean::inc(x_178);
lean::dec(x_3);
x_180 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_180, 1);
lean::inc(x_182);
lean::dec(x_180);
x_183 = l_Lean_IR_ExplicitBoxing_getDecl(x_178, x_5, x_182);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_185 = lean::cnstr_get(x_183, 1);
lean::inc(x_185);
lean::dec(x_183);
x_186 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_181, x_184);
lean::dec(x_184);
lean::dec(x_181);
x_187 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_179, x_5, x_185);
lean::dec(x_179);
if (x_186 == 0)
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_189 = lean::cnstr_get(x_187, 1);
lean::inc(x_189);
lean::dec(x_187);
x_190 = lean::cnstr_get(x_188, 0);
lean::inc(x_190);
x_191 = lean::cnstr_get(x_188, 1);
lean::inc(x_191);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_192 = x_188;
} else {
 lean::dec_ref(x_188);
 x_192 = lean::box(0);
}
x_193 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_193, 0, x_178);
lean::cnstr_set(x_193, 1, x_190);
x_194 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_194, 0, x_1);
lean::cnstr_set(x_194, 1, x_193);
lean::cnstr_set(x_194, 2, x_4);
lean::cnstr_set_scalar(x_194, sizeof(void*)*3, x_2);
x_195 = l_Lean_IR_reshape(x_191, x_194);
if (lean::is_scalar(x_192)) {
 x_196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_196 = x_192;
}
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_189);
return x_196;
}
else
{
obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_197 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_198 = lean_name_mk_string(x_178, x_197);
x_199 = lean::cnstr_get(x_187, 0);
lean::inc(x_199);
x_200 = lean::cnstr_get(x_187, 1);
lean::inc(x_200);
lean::dec(x_187);
x_201 = lean::cnstr_get(x_199, 0);
lean::inc(x_201);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
if (lean::is_exclusive(x_199)) {
 lean::cnstr_release(x_199, 0);
 lean::cnstr_release(x_199, 1);
 x_203 = x_199;
} else {
 lean::dec_ref(x_199);
 x_203 = lean::box(0);
}
x_204 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_204, 0, x_198);
lean::cnstr_set(x_204, 1, x_201);
x_205 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_205, 0, x_1);
lean::cnstr_set(x_205, 1, x_204);
lean::cnstr_set(x_205, 2, x_4);
lean::cnstr_set_scalar(x_205, sizeof(void*)*3, x_2);
x_206 = l_Lean_IR_reshape(x_202, x_205);
if (lean::is_scalar(x_203)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_203;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_200);
return x_207;
}
}
}
case 8:
{
uint8 x_208; 
x_208 = !lean::is_exclusive(x_3);
if (x_208 == 0)
{
obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; uint8 x_216; 
x_209 = lean::cnstr_get(x_3, 1);
x_210 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_209, x_5, x_6);
lean::dec(x_209);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_210, 1);
lean::inc(x_212);
lean::dec(x_210);
x_213 = lean::cnstr_get(x_211, 0);
lean::inc(x_213);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
lean::cnstr_set(x_3, 1, x_213);
x_215 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_212);
x_216 = !lean::is_exclusive(x_215);
if (x_216 == 0)
{
obj* x_217; obj* x_218; 
x_217 = lean::cnstr_get(x_215, 0);
x_218 = l_Lean_IR_reshape(x_214, x_217);
lean::cnstr_set(x_215, 0, x_218);
return x_215;
}
else
{
obj* x_219; obj* x_220; obj* x_221; obj* x_222; 
x_219 = lean::cnstr_get(x_215, 0);
x_220 = lean::cnstr_get(x_215, 1);
lean::inc(x_220);
lean::inc(x_219);
lean::dec(x_215);
x_221 = l_Lean_IR_reshape(x_214, x_219);
x_222 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_220);
return x_222;
}
}
else
{
obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_223 = lean::cnstr_get(x_3, 0);
x_224 = lean::cnstr_get(x_3, 1);
lean::inc(x_224);
lean::inc(x_223);
lean::dec(x_3);
x_225 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_224, x_5, x_6);
lean::dec(x_224);
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
x_227 = lean::cnstr_get(x_225, 1);
lean::inc(x_227);
lean::dec(x_225);
x_228 = lean::cnstr_get(x_226, 0);
lean::inc(x_228);
x_229 = lean::cnstr_get(x_226, 1);
lean::inc(x_229);
lean::dec(x_226);
x_230 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_230, 0, x_223);
lean::cnstr_set(x_230, 1, x_228);
x_231 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_230, x_4, x_5, x_227);
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_233 = lean::cnstr_get(x_231, 1);
lean::inc(x_233);
if (lean::is_exclusive(x_231)) {
 lean::cnstr_release(x_231, 0);
 lean::cnstr_release(x_231, 1);
 x_234 = x_231;
} else {
 lean::dec_ref(x_231);
 x_234 = lean::box(0);
}
x_235 = l_Lean_IR_reshape(x_229, x_232);
if (lean::is_scalar(x_234)) {
 x_236 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_236 = x_234;
}
lean::cnstr_set(x_236, 0, x_235);
lean::cnstr_set(x_236, 1, x_233);
return x_236;
}
}
default: 
{
obj* x_237; obj* x_238; 
x_237 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_237, 0, x_1);
lean::cnstr_set(x_237, 1, x_3);
lean::cnstr_set(x_237, 2, x_4);
lean::cnstr_set_scalar(x_237, sizeof(void*)*3, x_2);
x_238 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_6);
return x_238;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_1, x_7, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_8;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::array_fget(x_2, x_1);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = x_11;
x_13 = lean::array_fset(x_2, x_1, x_12);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::inc(x_3);
x_16 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_15, x_3, x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
lean::dec(x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_1, x_20);
x_22 = x_19;
x_23 = lean::array_fset(x_13, x_1, x_22);
lean::dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_4 = x_18;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_10, 0);
lean::inc(x_25);
lean::inc(x_3);
x_26 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_25, x_3, x_4);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
lean::dec(x_26);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_27);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_add(x_1, x_30);
x_32 = x_29;
x_33 = lean::array_fset(x_13, x_1, x_32);
lean::dec(x_1);
x_1 = x_31;
x_2 = x_33;
x_4 = x_28;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_3);
x_9 = lean::nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::array_fget(x_3, x_4);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean::array_get(x_14, x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1 + 1);
lean::dec(x_15);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8 x_26; 
lean::free_heap_obj(x_20);
x_26 = !lean::is_exclusive(x_11);
if (x_26 == 0)
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = lean::cnstr_get(x_11, 0);
lean::dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = lean::cnstr_get(x_28, 1);
x_32 = lean::unbox(x_22);
lean::dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean::box(13);
lean::inc(x_30);
x_35 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_30);
x_36 = lean::array_push(x_17, x_11);
x_37 = lean::array_push(x_18, x_35);
lean::cnstr_set(x_28, 1, x_37);
lean::cnstr_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_28, 0);
x_40 = lean::cnstr_get(x_28, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_28);
x_41 = lean::unbox(x_22);
lean::dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean::box(13);
lean::inc(x_39);
x_44 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
lean::cnstr_set_scalar(x_44, sizeof(void*)*3, x_16);
lean::cnstr_set(x_11, 0, x_39);
x_45 = lean::array_push(x_17, x_11);
x_46 = lean::array_push(x_18, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = lean::unbox(x_22);
lean::dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean::box(13);
lean::inc(x_50);
x_56 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_56, 0, x_50);
lean::cnstr_set(x_56, 1, x_54);
lean::cnstr_set(x_56, 2, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*3, x_16);
x_57 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_57, 0, x_50);
x_58 = lean::array_push(x_17, x_57);
x_59 = lean::array_push(x_18, x_56);
if (lean::is_scalar(x_52)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_52;
}
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
obj* x_62; 
lean::dec(x_22);
lean::dec(x_19);
x_62 = lean::array_push(x_17, x_11);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
obj* x_64; obj* x_65; uint8 x_66; uint8 x_67; 
x_64 = lean::cnstr_get(x_20, 0);
x_65 = lean::cnstr_get(x_20, 1);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_20);
x_66 = lean::unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_68 = x_11;
} else {
 lean::dec_ref(x_11);
 x_68 = lean::box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
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
x_73 = lean::unbox(x_64);
lean::dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean::box(13);
lean::inc(x_70);
x_76 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_76, 0, x_70);
lean::cnstr_set(x_76, 1, x_74);
lean::cnstr_set(x_76, 2, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*3, x_16);
if (lean::is_scalar(x_68)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_68;
}
lean::cnstr_set(x_77, 0, x_70);
x_78 = lean::array_push(x_17, x_77);
x_79 = lean::array_push(x_18, x_76);
if (lean::is_scalar(x_72)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_72;
}
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
obj* x_82; obj* x_83; 
lean::dec(x_64);
lean::dec(x_19);
x_82 = lean::array_push(x_17, x_11);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8 x_85; 
lean::dec(x_15);
x_85 = !lean::is_exclusive(x_5);
if (x_85 == 0)
{
obj* x_86; obj* x_87; 
x_86 = lean::cnstr_get(x_5, 0);
x_87 = lean::array_push(x_86, x_11);
lean::cnstr_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_5, 0);
x_90 = lean::cnstr_get(x_5, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_5);
x_91 = lean::array_push(x_89, x_11);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitFnBody___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; uint8 x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
lean::inc(x_6);
lean::inc(x_4);
x_12 = l_Lean_IR_LocalContext_addLocal(x_8, x_4, x_5, x_6);
x_13 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*3, x_9);
x_14 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_7, x_13, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_14, 1);
lean::inc(x_16);
lean::dec(x_14);
x_17 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_5, x_6, x_15, x_2, x_16);
lean::dec(x_2);
return x_17;
}
case 1:
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_1);
if (x_18 == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_2);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
x_24 = lean::cnstr_get(x_2, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_26 = lean::cnstr_get(x_2, 1);
x_27 = lean::cnstr_get(x_2, 2);
x_28 = lean::mk_nat_obj(0u);
lean::inc(x_24);
x_29 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_21, x_21, x_28, x_24);
lean::inc(x_27);
lean::inc(x_26);
lean::cnstr_set(x_2, 0, x_29);
x_30 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_22, x_2, x_3);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_30, 1);
lean::inc(x_32);
lean::dec(x_30);
lean::inc(x_31);
lean::inc(x_21);
lean::inc(x_20);
x_33 = l_Lean_IR_LocalContext_addJP(x_24, x_20, x_21, x_31);
x_34 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_26);
lean::cnstr_set(x_34, 2, x_27);
lean::cnstr_set_scalar(x_34, sizeof(void*)*3, x_25);
x_35 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_23, x_34, x_32);
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; 
x_37 = lean::cnstr_get(x_35, 0);
lean::cnstr_set(x_1, 3, x_37);
lean::cnstr_set(x_1, 2, x_31);
lean::cnstr_set(x_35, 0, x_1);
return x_35;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_35, 0);
x_39 = lean::cnstr_get(x_35, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_35);
lean::cnstr_set(x_1, 3, x_38);
lean::cnstr_set(x_1, 2, x_31);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_1);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_41 = lean::cnstr_get(x_1, 0);
x_42 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_44 = lean::cnstr_get(x_1, 3);
x_45 = lean::cnstr_get(x_2, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_47 = lean::cnstr_get(x_2, 1);
x_48 = lean::cnstr_get(x_2, 2);
lean::inc(x_48);
lean::inc(x_47);
lean::inc(x_45);
lean::dec(x_2);
x_49 = lean::mk_nat_obj(0u);
lean::inc(x_45);
x_50 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_42, x_42, x_49, x_45);
lean::inc(x_48);
lean::inc(x_47);
x_51 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
lean::cnstr_set(x_51, 2, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*3, x_46);
x_52 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_43, x_51, x_3);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
lean::dec(x_52);
lean::inc(x_53);
lean::inc(x_42);
lean::inc(x_41);
x_55 = l_Lean_IR_LocalContext_addJP(x_45, x_41, x_42, x_53);
x_56 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_47);
lean::cnstr_set(x_56, 2, x_48);
lean::cnstr_set_scalar(x_56, sizeof(void*)*3, x_46);
x_57 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_44, x_56, x_54);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_60 = x_57;
} else {
 lean::dec_ref(x_57);
 x_60 = lean::box(0);
}
lean::cnstr_set(x_1, 3, x_58);
lean::cnstr_set(x_1, 2, x_53);
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_1);
lean::cnstr_set(x_61, 1, x_59);
return x_61;
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_62 = lean::cnstr_get(x_1, 0);
x_63 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_1, 2);
x_65 = lean::cnstr_get(x_1, 3);
lean::inc(x_65);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_2, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_68 = lean::cnstr_get(x_2, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_2, 2);
lean::inc(x_69);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_70 = x_2;
} else {
 lean::dec_ref(x_2);
 x_70 = lean::box(0);
}
x_71 = lean::mk_nat_obj(0u);
lean::inc(x_66);
x_72 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_63, x_63, x_71, x_66);
lean::inc(x_69);
lean::inc(x_68);
if (lean::is_scalar(x_70)) {
 x_73 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_73 = x_70;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_68);
lean::cnstr_set(x_73, 2, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*3, x_67);
x_74 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_64, x_73, x_3);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_74, 1);
lean::inc(x_76);
lean::dec(x_74);
lean::inc(x_75);
lean::inc(x_63);
lean::inc(x_62);
x_77 = l_Lean_IR_LocalContext_addJP(x_66, x_62, x_63, x_75);
x_78 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_68);
lean::cnstr_set(x_78, 2, x_69);
lean::cnstr_set_scalar(x_78, sizeof(void*)*3, x_67);
x_79 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_65, x_78, x_76);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_79, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_82 = x_79;
} else {
 lean::dec_ref(x_79);
 x_82 = lean::box(0);
}
x_83 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_83, 0, x_62);
lean::cnstr_set(x_83, 1, x_63);
lean::cnstr_set(x_83, 2, x_75);
lean::cnstr_set(x_83, 3, x_80);
if (lean::is_scalar(x_82)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_82;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
return x_84;
}
}
case 4:
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_1);
if (x_85 == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; uint8 x_92; 
x_86 = lean::cnstr_get(x_1, 2);
x_87 = lean::cnstr_get(x_1, 3);
lean::inc(x_2);
x_88 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_87, x_2, x_3);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_88, 1);
lean::inc(x_90);
lean::dec(x_88);
x_91 = l_Lean_IR_ExplicitBoxing_getVarType(x_86, x_2, x_90);
lean::dec(x_2);
x_92 = !lean::is_exclusive(x_91);
if (x_92 == 0)
{
obj* x_93; obj* x_94; uint8 x_95; uint8 x_96; uint8 x_97; 
x_93 = lean::cnstr_get(x_91, 0);
x_94 = lean::cnstr_get(x_91, 1);
x_95 = 5;
x_96 = lean::unbox(x_93);
x_97 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_96, x_95);
if (x_97 == 0)
{
obj* x_98; uint8 x_99; 
lean::free_heap_obj(x_91);
x_98 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_94);
x_99 = !lean::is_exclusive(x_98);
if (x_99 == 0)
{
obj* x_100; uint8 x_101; obj* x_102; obj* x_103; 
x_100 = lean::cnstr_get(x_98, 0);
x_101 = lean::unbox(x_93);
lean::dec(x_93);
x_102 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_101);
lean::inc(x_100);
lean::cnstr_set(x_1, 3, x_89);
lean::cnstr_set(x_1, 2, x_100);
x_103 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_102);
lean::cnstr_set(x_103, 2, x_1);
lean::cnstr_set_scalar(x_103, sizeof(void*)*3, x_95);
lean::cnstr_set(x_98, 0, x_103);
return x_98;
}
else
{
obj* x_104; obj* x_105; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_98, 0);
x_105 = lean::cnstr_get(x_98, 1);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_98);
x_106 = lean::unbox(x_93);
lean::dec(x_93);
x_107 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_106);
lean::inc(x_104);
lean::cnstr_set(x_1, 3, x_89);
lean::cnstr_set(x_1, 2, x_104);
x_108 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set(x_108, 1, x_107);
lean::cnstr_set(x_108, 2, x_1);
lean::cnstr_set_scalar(x_108, sizeof(void*)*3, x_95);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
return x_109;
}
}
else
{
lean::dec(x_93);
lean::cnstr_set(x_1, 3, x_89);
lean::cnstr_set(x_91, 0, x_1);
return x_91;
}
}
else
{
obj* x_110; obj* x_111; uint8 x_112; uint8 x_113; uint8 x_114; 
x_110 = lean::cnstr_get(x_91, 0);
x_111 = lean::cnstr_get(x_91, 1);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_91);
x_112 = 5;
x_113 = lean::unbox(x_110);
x_114 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_113, x_112);
if (x_114 == 0)
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; 
x_115 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_111);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_115, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_118 = x_115;
} else {
 lean::dec_ref(x_115);
 x_118 = lean::box(0);
}
x_119 = lean::unbox(x_110);
lean::dec(x_110);
x_120 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_119);
lean::inc(x_116);
lean::cnstr_set(x_1, 3, x_89);
lean::cnstr_set(x_1, 2, x_116);
x_121 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_121, 0, x_116);
lean::cnstr_set(x_121, 1, x_120);
lean::cnstr_set(x_121, 2, x_1);
lean::cnstr_set_scalar(x_121, sizeof(void*)*3, x_112);
if (lean::is_scalar(x_118)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_118;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_117);
return x_122;
}
else
{
obj* x_123; 
lean::dec(x_110);
lean::cnstr_set(x_1, 3, x_89);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_1);
lean::cnstr_set(x_123, 1, x_111);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; uint8 x_135; uint8 x_136; uint8 x_137; 
x_124 = lean::cnstr_get(x_1, 0);
x_125 = lean::cnstr_get(x_1, 1);
x_126 = lean::cnstr_get(x_1, 2);
x_127 = lean::cnstr_get(x_1, 3);
lean::inc(x_127);
lean::inc(x_126);
lean::inc(x_125);
lean::inc(x_124);
lean::dec(x_1);
lean::inc(x_2);
x_128 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_127, x_2, x_3);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_128, 1);
lean::inc(x_130);
lean::dec(x_128);
x_131 = l_Lean_IR_ExplicitBoxing_getVarType(x_126, x_2, x_130);
lean::dec(x_2);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_131, 1);
lean::inc(x_133);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_134 = x_131;
} else {
 lean::dec_ref(x_131);
 x_134 = lean::box(0);
}
x_135 = 5;
x_136 = lean::unbox(x_132);
x_137 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_136, x_135);
if (x_137 == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; uint8 x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_134);
x_138 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_133);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_138, 1);
lean::inc(x_140);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_141 = x_138;
} else {
 lean::dec_ref(x_138);
 x_141 = lean::box(0);
}
x_142 = lean::unbox(x_132);
lean::dec(x_132);
x_143 = l_Lean_IR_ExplicitBoxing_mkCast(x_126, x_142);
lean::inc(x_139);
x_144 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_144, 0, x_124);
lean::cnstr_set(x_144, 1, x_125);
lean::cnstr_set(x_144, 2, x_139);
lean::cnstr_set(x_144, 3, x_129);
x_145 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_145, 0, x_139);
lean::cnstr_set(x_145, 1, x_143);
lean::cnstr_set(x_145, 2, x_144);
lean::cnstr_set_scalar(x_145, sizeof(void*)*3, x_135);
if (lean::is_scalar(x_141)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_141;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_140);
return x_146;
}
else
{
obj* x_147; obj* x_148; 
lean::dec(x_132);
x_147 = lean::alloc_cnstr(4, 4, 0);
lean::cnstr_set(x_147, 0, x_124);
lean::cnstr_set(x_147, 1, x_125);
lean::cnstr_set(x_147, 2, x_126);
lean::cnstr_set(x_147, 3, x_129);
if (lean::is_scalar(x_134)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_134;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_133);
return x_148;
}
}
}
case 5:
{
uint8 x_149; 
x_149 = !lean::is_exclusive(x_1);
if (x_149 == 0)
{
obj* x_150; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; uint8 x_157; 
x_150 = lean::cnstr_get(x_1, 3);
x_151 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_152 = lean::cnstr_get(x_1, 4);
lean::inc(x_2);
x_153 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_152, x_2, x_3);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_153, 1);
lean::inc(x_155);
lean::dec(x_153);
x_156 = l_Lean_IR_ExplicitBoxing_getVarType(x_150, x_2, x_155);
lean::dec(x_2);
x_157 = !lean::is_exclusive(x_156);
if (x_157 == 0)
{
obj* x_158; obj* x_159; uint8 x_160; uint8 x_161; 
x_158 = lean::cnstr_get(x_156, 0);
x_159 = lean::cnstr_get(x_156, 1);
x_160 = lean::unbox(x_158);
x_161 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_160, x_151);
if (x_161 == 0)
{
obj* x_162; uint8 x_163; 
lean::free_heap_obj(x_156);
x_162 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_159);
x_163 = !lean::is_exclusive(x_162);
if (x_163 == 0)
{
obj* x_164; uint8 x_165; obj* x_166; obj* x_167; 
x_164 = lean::cnstr_get(x_162, 0);
x_165 = lean::unbox(x_158);
lean::dec(x_158);
x_166 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_165);
lean::inc(x_164);
lean::cnstr_set(x_1, 4, x_154);
lean::cnstr_set(x_1, 3, x_164);
x_167 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_167, 0, x_164);
lean::cnstr_set(x_167, 1, x_166);
lean::cnstr_set(x_167, 2, x_1);
lean::cnstr_set_scalar(x_167, sizeof(void*)*3, x_151);
lean::cnstr_set(x_162, 0, x_167);
return x_162;
}
else
{
obj* x_168; obj* x_169; uint8 x_170; obj* x_171; obj* x_172; obj* x_173; 
x_168 = lean::cnstr_get(x_162, 0);
x_169 = lean::cnstr_get(x_162, 1);
lean::inc(x_169);
lean::inc(x_168);
lean::dec(x_162);
x_170 = lean::unbox(x_158);
lean::dec(x_158);
x_171 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_170);
lean::inc(x_168);
lean::cnstr_set(x_1, 4, x_154);
lean::cnstr_set(x_1, 3, x_168);
x_172 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set(x_172, 1, x_171);
lean::cnstr_set(x_172, 2, x_1);
lean::cnstr_set_scalar(x_172, sizeof(void*)*3, x_151);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_169);
return x_173;
}
}
else
{
lean::dec(x_158);
lean::cnstr_set(x_1, 4, x_154);
lean::cnstr_set(x_156, 0, x_1);
return x_156;
}
}
else
{
obj* x_174; obj* x_175; uint8 x_176; uint8 x_177; 
x_174 = lean::cnstr_get(x_156, 0);
x_175 = lean::cnstr_get(x_156, 1);
lean::inc(x_175);
lean::inc(x_174);
lean::dec(x_156);
x_176 = lean::unbox(x_174);
x_177 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_176, x_151);
if (x_177 == 0)
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; obj* x_184; obj* x_185; 
x_178 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_175);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_180 = lean::cnstr_get(x_178, 1);
lean::inc(x_180);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 x_181 = x_178;
} else {
 lean::dec_ref(x_178);
 x_181 = lean::box(0);
}
x_182 = lean::unbox(x_174);
lean::dec(x_174);
x_183 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_182);
lean::inc(x_179);
lean::cnstr_set(x_1, 4, x_154);
lean::cnstr_set(x_1, 3, x_179);
x_184 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_184, 0, x_179);
lean::cnstr_set(x_184, 1, x_183);
lean::cnstr_set(x_184, 2, x_1);
lean::cnstr_set_scalar(x_184, sizeof(void*)*3, x_151);
if (lean::is_scalar(x_181)) {
 x_185 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_185 = x_181;
}
lean::cnstr_set(x_185, 0, x_184);
lean::cnstr_set(x_185, 1, x_180);
return x_185;
}
else
{
obj* x_186; 
lean::dec(x_174);
lean::cnstr_set(x_1, 4, x_154);
x_186 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_186, 0, x_1);
lean::cnstr_set(x_186, 1, x_175);
return x_186;
}
}
}
else
{
obj* x_187; obj* x_188; obj* x_189; obj* x_190; uint8 x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; uint8 x_201; 
x_187 = lean::cnstr_get(x_1, 0);
x_188 = lean::cnstr_get(x_1, 1);
x_189 = lean::cnstr_get(x_1, 2);
x_190 = lean::cnstr_get(x_1, 3);
x_191 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_192 = lean::cnstr_get(x_1, 4);
lean::inc(x_192);
lean::inc(x_190);
lean::inc(x_189);
lean::inc(x_188);
lean::inc(x_187);
lean::dec(x_1);
lean::inc(x_2);
x_193 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_192, x_2, x_3);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_195 = lean::cnstr_get(x_193, 1);
lean::inc(x_195);
lean::dec(x_193);
x_196 = l_Lean_IR_ExplicitBoxing_getVarType(x_190, x_2, x_195);
lean::dec(x_2);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
x_198 = lean::cnstr_get(x_196, 1);
lean::inc(x_198);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 lean::cnstr_release(x_196, 1);
 x_199 = x_196;
} else {
 lean::dec_ref(x_196);
 x_199 = lean::box(0);
}
x_200 = lean::unbox(x_197);
x_201 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_200, x_191);
if (x_201 == 0)
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_199);
x_202 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_198);
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
x_204 = lean::cnstr_get(x_202, 1);
lean::inc(x_204);
if (lean::is_exclusive(x_202)) {
 lean::cnstr_release(x_202, 0);
 lean::cnstr_release(x_202, 1);
 x_205 = x_202;
} else {
 lean::dec_ref(x_202);
 x_205 = lean::box(0);
}
x_206 = lean::unbox(x_197);
lean::dec(x_197);
x_207 = l_Lean_IR_ExplicitBoxing_mkCast(x_190, x_206);
lean::inc(x_203);
x_208 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_208, 0, x_187);
lean::cnstr_set(x_208, 1, x_188);
lean::cnstr_set(x_208, 2, x_189);
lean::cnstr_set(x_208, 3, x_203);
lean::cnstr_set(x_208, 4, x_194);
lean::cnstr_set_scalar(x_208, sizeof(void*)*5, x_191);
x_209 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_209, 0, x_203);
lean::cnstr_set(x_209, 1, x_207);
lean::cnstr_set(x_209, 2, x_208);
lean::cnstr_set_scalar(x_209, sizeof(void*)*3, x_191);
if (lean::is_scalar(x_205)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_205;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_204);
return x_210;
}
else
{
obj* x_211; obj* x_212; 
lean::dec(x_197);
x_211 = lean::alloc_cnstr(5, 5, 1);
lean::cnstr_set(x_211, 0, x_187);
lean::cnstr_set(x_211, 1, x_188);
lean::cnstr_set(x_211, 2, x_189);
lean::cnstr_set(x_211, 3, x_190);
lean::cnstr_set(x_211, 4, x_194);
lean::cnstr_set_scalar(x_211, sizeof(void*)*5, x_191);
if (lean::is_scalar(x_199)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_199;
}
lean::cnstr_set(x_212, 0, x_211);
lean::cnstr_set(x_212, 1, x_198);
return x_212;
}
}
}
case 9:
{
uint8 x_213; 
x_213 = !lean::is_exclusive(x_1);
if (x_213 == 0)
{
obj* x_214; obj* x_215; uint8 x_216; 
x_214 = lean::cnstr_get(x_1, 1);
x_215 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_214, x_2, x_3);
x_216 = !lean::is_exclusive(x_215);
if (x_216 == 0)
{
obj* x_217; 
x_217 = lean::cnstr_get(x_215, 0);
lean::cnstr_set(x_1, 1, x_217);
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
x_220 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_220, 0, x_1);
lean::cnstr_set(x_220, 1, x_219);
return x_220;
}
}
else
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_221 = lean::cnstr_get(x_1, 0);
x_222 = lean::cnstr_get(x_1, 1);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_1);
x_223 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_222, x_2, x_3);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_225 = lean::cnstr_get(x_223, 1);
lean::inc(x_225);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_226 = x_223;
} else {
 lean::dec_ref(x_223);
 x_226 = lean::box(0);
}
x_227 = lean::alloc_cnstr(9, 2, 0);
lean::cnstr_set(x_227, 0, x_221);
lean::cnstr_set(x_227, 1, x_224);
if (lean::is_scalar(x_226)) {
 x_228 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_228 = x_226;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_225);
return x_228;
}
}
case 10:
{
uint8 x_229; 
x_229 = !lean::is_exclusive(x_1);
if (x_229 == 0)
{
obj* x_230; obj* x_231; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; uint8 x_238; 
x_230 = lean::cnstr_get(x_1, 1);
x_231 = lean::cnstr_get(x_1, 2);
x_232 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_231);
x_233 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_234 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_233, x_231, x_2, x_3);
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_236 = lean::cnstr_get(x_234, 1);
lean::inc(x_236);
lean::dec(x_234);
x_237 = l_Lean_IR_ExplicitBoxing_getVarType(x_230, x_2, x_236);
lean::dec(x_2);
x_238 = !lean::is_exclusive(x_237);
if (x_238 == 0)
{
obj* x_239; obj* x_240; uint8 x_241; uint8 x_242; 
x_239 = lean::cnstr_get(x_237, 0);
x_240 = lean::cnstr_get(x_237, 1);
x_241 = lean::unbox(x_239);
x_242 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_241, x_232);
if (x_242 == 0)
{
obj* x_243; uint8 x_244; 
lean::free_heap_obj(x_237);
x_243 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_240);
x_244 = !lean::is_exclusive(x_243);
if (x_244 == 0)
{
obj* x_245; uint8 x_246; obj* x_247; obj* x_248; 
x_245 = lean::cnstr_get(x_243, 0);
x_246 = lean::unbox(x_239);
lean::dec(x_239);
x_247 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_246);
lean::inc(x_245);
lean::cnstr_set(x_1, 2, x_235);
lean::cnstr_set(x_1, 1, x_245);
x_248 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_248, 0, x_245);
lean::cnstr_set(x_248, 1, x_247);
lean::cnstr_set(x_248, 2, x_1);
lean::cnstr_set_scalar(x_248, sizeof(void*)*3, x_232);
lean::cnstr_set(x_243, 0, x_248);
return x_243;
}
else
{
obj* x_249; obj* x_250; uint8 x_251; obj* x_252; obj* x_253; obj* x_254; 
x_249 = lean::cnstr_get(x_243, 0);
x_250 = lean::cnstr_get(x_243, 1);
lean::inc(x_250);
lean::inc(x_249);
lean::dec(x_243);
x_251 = lean::unbox(x_239);
lean::dec(x_239);
x_252 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_251);
lean::inc(x_249);
lean::cnstr_set(x_1, 2, x_235);
lean::cnstr_set(x_1, 1, x_249);
x_253 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_253, 0, x_249);
lean::cnstr_set(x_253, 1, x_252);
lean::cnstr_set(x_253, 2, x_1);
lean::cnstr_set_scalar(x_253, sizeof(void*)*3, x_232);
x_254 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_254, 0, x_253);
lean::cnstr_set(x_254, 1, x_250);
return x_254;
}
}
else
{
lean::dec(x_239);
lean::cnstr_set(x_1, 2, x_235);
lean::cnstr_set(x_237, 0, x_1);
return x_237;
}
}
else
{
obj* x_255; obj* x_256; uint8 x_257; uint8 x_258; 
x_255 = lean::cnstr_get(x_237, 0);
x_256 = lean::cnstr_get(x_237, 1);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_237);
x_257 = lean::unbox(x_255);
x_258 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_257, x_232);
if (x_258 == 0)
{
obj* x_259; obj* x_260; obj* x_261; obj* x_262; uint8 x_263; obj* x_264; obj* x_265; obj* x_266; 
x_259 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_256);
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_259, 1);
lean::inc(x_261);
if (lean::is_exclusive(x_259)) {
 lean::cnstr_release(x_259, 0);
 lean::cnstr_release(x_259, 1);
 x_262 = x_259;
} else {
 lean::dec_ref(x_259);
 x_262 = lean::box(0);
}
x_263 = lean::unbox(x_255);
lean::dec(x_255);
x_264 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_263);
lean::inc(x_260);
lean::cnstr_set(x_1, 2, x_235);
lean::cnstr_set(x_1, 1, x_260);
x_265 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_265, 0, x_260);
lean::cnstr_set(x_265, 1, x_264);
lean::cnstr_set(x_265, 2, x_1);
lean::cnstr_set_scalar(x_265, sizeof(void*)*3, x_232);
if (lean::is_scalar(x_262)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_262;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_261);
return x_266;
}
else
{
obj* x_267; 
lean::dec(x_255);
lean::cnstr_set(x_1, 2, x_235);
x_267 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_267, 0, x_1);
lean::cnstr_set(x_267, 1, x_256);
return x_267;
}
}
}
else
{
obj* x_268; obj* x_269; obj* x_270; uint8 x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; uint8 x_280; uint8 x_281; 
x_268 = lean::cnstr_get(x_1, 0);
x_269 = lean::cnstr_get(x_1, 1);
x_270 = lean::cnstr_get(x_1, 2);
lean::inc(x_270);
lean::inc(x_269);
lean::inc(x_268);
lean::dec(x_1);
x_271 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_270);
x_272 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_273 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_272, x_270, x_2, x_3);
x_274 = lean::cnstr_get(x_273, 0);
lean::inc(x_274);
x_275 = lean::cnstr_get(x_273, 1);
lean::inc(x_275);
lean::dec(x_273);
x_276 = l_Lean_IR_ExplicitBoxing_getVarType(x_269, x_2, x_275);
lean::dec(x_2);
x_277 = lean::cnstr_get(x_276, 0);
lean::inc(x_277);
x_278 = lean::cnstr_get(x_276, 1);
lean::inc(x_278);
if (lean::is_exclusive(x_276)) {
 lean::cnstr_release(x_276, 0);
 lean::cnstr_release(x_276, 1);
 x_279 = x_276;
} else {
 lean::dec_ref(x_276);
 x_279 = lean::box(0);
}
x_280 = lean::unbox(x_277);
x_281 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_280, x_271);
if (x_281 == 0)
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; uint8 x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
lean::dec(x_279);
x_282 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_278);
x_283 = lean::cnstr_get(x_282, 0);
lean::inc(x_283);
x_284 = lean::cnstr_get(x_282, 1);
lean::inc(x_284);
if (lean::is_exclusive(x_282)) {
 lean::cnstr_release(x_282, 0);
 lean::cnstr_release(x_282, 1);
 x_285 = x_282;
} else {
 lean::dec_ref(x_282);
 x_285 = lean::box(0);
}
x_286 = lean::unbox(x_277);
lean::dec(x_277);
x_287 = l_Lean_IR_ExplicitBoxing_mkCast(x_269, x_286);
lean::inc(x_283);
x_288 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_288, 0, x_268);
lean::cnstr_set(x_288, 1, x_283);
lean::cnstr_set(x_288, 2, x_274);
x_289 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_289, 0, x_283);
lean::cnstr_set(x_289, 1, x_287);
lean::cnstr_set(x_289, 2, x_288);
lean::cnstr_set_scalar(x_289, sizeof(void*)*3, x_271);
if (lean::is_scalar(x_285)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_285;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_284);
return x_290;
}
else
{
obj* x_291; obj* x_292; 
lean::dec(x_277);
x_291 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_291, 0, x_268);
lean::cnstr_set(x_291, 1, x_269);
lean::cnstr_set(x_291, 2, x_274);
if (lean::is_scalar(x_279)) {
 x_292 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_292 = x_279;
}
lean::cnstr_set(x_292, 0, x_291);
lean::cnstr_set(x_292, 1, x_278);
return x_292;
}
}
}
case 11:
{
uint8 x_293; 
x_293 = !lean::is_exclusive(x_1);
if (x_293 == 0)
{
obj* x_294; obj* x_295; 
x_294 = lean::cnstr_get(x_1, 0);
x_295 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean::obj_tag(x_294) == 0)
{
obj* x_296; obj* x_297; uint8 x_298; 
x_296 = lean::cnstr_get(x_295, 0);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_295, 1);
lean::inc(x_297);
lean::dec(x_295);
x_298 = !lean::is_exclusive(x_294);
if (x_298 == 0)
{
obj* x_299; obj* x_300; uint8 x_301; 
x_299 = lean::cnstr_get(x_294, 0);
x_300 = l_Lean_IR_ExplicitBoxing_getVarType(x_299, x_2, x_297);
lean::dec(x_2);
x_301 = !lean::is_exclusive(x_300);
if (x_301 == 0)
{
obj* x_302; obj* x_303; uint8 x_304; uint8 x_305; uint8 x_306; 
x_302 = lean::cnstr_get(x_300, 0);
x_303 = lean::cnstr_get(x_300, 1);
x_304 = lean::unbox(x_302);
x_305 = lean::unbox(x_296);
x_306 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_304, x_305);
if (x_306 == 0)
{
obj* x_307; uint8 x_308; 
lean::free_heap_obj(x_300);
x_307 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_303);
x_308 = !lean::is_exclusive(x_307);
if (x_308 == 0)
{
obj* x_309; uint8 x_310; obj* x_311; obj* x_312; uint8 x_313; 
x_309 = lean::cnstr_get(x_307, 0);
x_310 = lean::unbox(x_302);
lean::dec(x_302);
x_311 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_310);
lean::inc(x_309);
lean::cnstr_set(x_294, 0, x_309);
x_312 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_312, 0, x_309);
lean::cnstr_set(x_312, 1, x_311);
lean::cnstr_set(x_312, 2, x_1);
x_313 = lean::unbox(x_296);
lean::dec(x_296);
lean::cnstr_set_scalar(x_312, sizeof(void*)*3, x_313);
lean::cnstr_set(x_307, 0, x_312);
return x_307;
}
else
{
obj* x_314; obj* x_315; uint8 x_316; obj* x_317; obj* x_318; uint8 x_319; obj* x_320; 
x_314 = lean::cnstr_get(x_307, 0);
x_315 = lean::cnstr_get(x_307, 1);
lean::inc(x_315);
lean::inc(x_314);
lean::dec(x_307);
x_316 = lean::unbox(x_302);
lean::dec(x_302);
x_317 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_316);
lean::inc(x_314);
lean::cnstr_set(x_294, 0, x_314);
x_318 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_318, 0, x_314);
lean::cnstr_set(x_318, 1, x_317);
lean::cnstr_set(x_318, 2, x_1);
x_319 = lean::unbox(x_296);
lean::dec(x_296);
lean::cnstr_set_scalar(x_318, sizeof(void*)*3, x_319);
x_320 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_320, 0, x_318);
lean::cnstr_set(x_320, 1, x_315);
return x_320;
}
}
else
{
lean::dec(x_302);
lean::dec(x_296);
lean::cnstr_set(x_300, 0, x_1);
return x_300;
}
}
else
{
obj* x_321; obj* x_322; uint8 x_323; uint8 x_324; uint8 x_325; 
x_321 = lean::cnstr_get(x_300, 0);
x_322 = lean::cnstr_get(x_300, 1);
lean::inc(x_322);
lean::inc(x_321);
lean::dec(x_300);
x_323 = lean::unbox(x_321);
x_324 = lean::unbox(x_296);
x_325 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_323, x_324);
if (x_325 == 0)
{
obj* x_326; obj* x_327; obj* x_328; obj* x_329; uint8 x_330; obj* x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_326 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_322);
x_327 = lean::cnstr_get(x_326, 0);
lean::inc(x_327);
x_328 = lean::cnstr_get(x_326, 1);
lean::inc(x_328);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 x_329 = x_326;
} else {
 lean::dec_ref(x_326);
 x_329 = lean::box(0);
}
x_330 = lean::unbox(x_321);
lean::dec(x_321);
x_331 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_330);
lean::inc(x_327);
lean::cnstr_set(x_294, 0, x_327);
x_332 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_331);
lean::cnstr_set(x_332, 2, x_1);
x_333 = lean::unbox(x_296);
lean::dec(x_296);
lean::cnstr_set_scalar(x_332, sizeof(void*)*3, x_333);
if (lean::is_scalar(x_329)) {
 x_334 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_334 = x_329;
}
lean::cnstr_set(x_334, 0, x_332);
lean::cnstr_set(x_334, 1, x_328);
return x_334;
}
else
{
obj* x_335; 
lean::dec(x_321);
lean::dec(x_296);
x_335 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_335, 0, x_1);
lean::cnstr_set(x_335, 1, x_322);
return x_335;
}
}
}
else
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; uint8 x_341; uint8 x_342; uint8 x_343; 
x_336 = lean::cnstr_get(x_294, 0);
lean::inc(x_336);
lean::dec(x_294);
x_337 = l_Lean_IR_ExplicitBoxing_getVarType(x_336, x_2, x_297);
lean::dec(x_2);
x_338 = lean::cnstr_get(x_337, 0);
lean::inc(x_338);
x_339 = lean::cnstr_get(x_337, 1);
lean::inc(x_339);
if (lean::is_exclusive(x_337)) {
 lean::cnstr_release(x_337, 0);
 lean::cnstr_release(x_337, 1);
 x_340 = x_337;
} else {
 lean::dec_ref(x_337);
 x_340 = lean::box(0);
}
x_341 = lean::unbox(x_338);
x_342 = lean::unbox(x_296);
x_343 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_341, x_342);
if (x_343 == 0)
{
obj* x_344; obj* x_345; obj* x_346; obj* x_347; uint8 x_348; obj* x_349; obj* x_350; obj* x_351; uint8 x_352; obj* x_353; 
lean::dec(x_340);
x_344 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_339);
x_345 = lean::cnstr_get(x_344, 0);
lean::inc(x_345);
x_346 = lean::cnstr_get(x_344, 1);
lean::inc(x_346);
if (lean::is_exclusive(x_344)) {
 lean::cnstr_release(x_344, 0);
 lean::cnstr_release(x_344, 1);
 x_347 = x_344;
} else {
 lean::dec_ref(x_344);
 x_347 = lean::box(0);
}
x_348 = lean::unbox(x_338);
lean::dec(x_338);
x_349 = l_Lean_IR_ExplicitBoxing_mkCast(x_336, x_348);
lean::inc(x_345);
x_350 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_350, 0, x_345);
lean::cnstr_set(x_1, 0, x_350);
x_351 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_351, 0, x_345);
lean::cnstr_set(x_351, 1, x_349);
lean::cnstr_set(x_351, 2, x_1);
x_352 = lean::unbox(x_296);
lean::dec(x_296);
lean::cnstr_set_scalar(x_351, sizeof(void*)*3, x_352);
if (lean::is_scalar(x_347)) {
 x_353 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_353 = x_347;
}
lean::cnstr_set(x_353, 0, x_351);
lean::cnstr_set(x_353, 1, x_346);
return x_353;
}
else
{
obj* x_354; obj* x_355; 
lean::dec(x_338);
lean::dec(x_296);
x_354 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_354, 0, x_336);
lean::cnstr_set(x_1, 0, x_354);
if (lean::is_scalar(x_340)) {
 x_355 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_355 = x_340;
}
lean::cnstr_set(x_355, 0, x_1);
lean::cnstr_set(x_355, 1, x_339);
return x_355;
}
}
}
else
{
uint8 x_356; 
lean::dec(x_2);
x_356 = !lean::is_exclusive(x_295);
if (x_356 == 0)
{
obj* x_357; 
x_357 = lean::cnstr_get(x_295, 0);
lean::dec(x_357);
lean::cnstr_set(x_295, 0, x_1);
return x_295;
}
else
{
obj* x_358; obj* x_359; 
x_358 = lean::cnstr_get(x_295, 1);
lean::inc(x_358);
lean::dec(x_295);
x_359 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_359, 0, x_1);
lean::cnstr_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
obj* x_360; obj* x_361; 
x_360 = lean::cnstr_get(x_1, 0);
lean::inc(x_360);
lean::dec(x_1);
x_361 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean::obj_tag(x_360) == 0)
{
obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; uint8 x_370; uint8 x_371; uint8 x_372; 
x_362 = lean::cnstr_get(x_361, 0);
lean::inc(x_362);
x_363 = lean::cnstr_get(x_361, 1);
lean::inc(x_363);
lean::dec(x_361);
x_364 = lean::cnstr_get(x_360, 0);
lean::inc(x_364);
if (lean::is_exclusive(x_360)) {
 lean::cnstr_release(x_360, 0);
 x_365 = x_360;
} else {
 lean::dec_ref(x_360);
 x_365 = lean::box(0);
}
x_366 = l_Lean_IR_ExplicitBoxing_getVarType(x_364, x_2, x_363);
lean::dec(x_2);
x_367 = lean::cnstr_get(x_366, 0);
lean::inc(x_367);
x_368 = lean::cnstr_get(x_366, 1);
lean::inc(x_368);
if (lean::is_exclusive(x_366)) {
 lean::cnstr_release(x_366, 0);
 lean::cnstr_release(x_366, 1);
 x_369 = x_366;
} else {
 lean::dec_ref(x_366);
 x_369 = lean::box(0);
}
x_370 = lean::unbox(x_367);
x_371 = lean::unbox(x_362);
x_372 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_370, x_371);
if (x_372 == 0)
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; uint8 x_382; obj* x_383; 
lean::dec(x_369);
x_373 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_368);
x_374 = lean::cnstr_get(x_373, 0);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_373, 1);
lean::inc(x_375);
if (lean::is_exclusive(x_373)) {
 lean::cnstr_release(x_373, 0);
 lean::cnstr_release(x_373, 1);
 x_376 = x_373;
} else {
 lean::dec_ref(x_373);
 x_376 = lean::box(0);
}
x_377 = lean::unbox(x_367);
lean::dec(x_367);
x_378 = l_Lean_IR_ExplicitBoxing_mkCast(x_364, x_377);
lean::inc(x_374);
if (lean::is_scalar(x_365)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_365;
}
lean::cnstr_set(x_379, 0, x_374);
x_380 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_380, 0, x_379);
x_381 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_381, 0, x_374);
lean::cnstr_set(x_381, 1, x_378);
lean::cnstr_set(x_381, 2, x_380);
x_382 = lean::unbox(x_362);
lean::dec(x_362);
lean::cnstr_set_scalar(x_381, sizeof(void*)*3, x_382);
if (lean::is_scalar(x_376)) {
 x_383 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_383 = x_376;
}
lean::cnstr_set(x_383, 0, x_381);
lean::cnstr_set(x_383, 1, x_375);
return x_383;
}
else
{
obj* x_384; obj* x_385; obj* x_386; 
lean::dec(x_367);
lean::dec(x_362);
if (lean::is_scalar(x_365)) {
 x_384 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_384 = x_365;
}
lean::cnstr_set(x_384, 0, x_364);
x_385 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_385, 0, x_384);
if (lean::is_scalar(x_369)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_369;
}
lean::cnstr_set(x_386, 0, x_385);
lean::cnstr_set(x_386, 1, x_368);
return x_386;
}
}
else
{
obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
lean::dec(x_2);
x_387 = lean::cnstr_get(x_361, 1);
lean::inc(x_387);
if (lean::is_exclusive(x_361)) {
 lean::cnstr_release(x_361, 0);
 lean::cnstr_release(x_361, 1);
 x_388 = x_361;
} else {
 lean::dec_ref(x_361);
 x_388 = lean::box(0);
}
x_389 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_389, 0, x_360);
if (lean::is_scalar(x_388)) {
 x_390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_390 = x_388;
}
lean::cnstr_set(x_390, 0, x_389);
lean::cnstr_set(x_390, 1, x_387);
return x_390;
}
}
}
case 12:
{
uint8 x_391; 
x_391 = !lean::is_exclusive(x_1);
if (x_391 == 0)
{
obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; uint8 x_400; 
x_392 = lean::cnstr_get(x_1, 0);
x_393 = lean::cnstr_get(x_1, 1);
x_394 = l_Lean_IR_ExplicitBoxing_getJPParams(x_392, x_2, x_3);
x_395 = lean::cnstr_get(x_394, 0);
lean::inc(x_395);
x_396 = lean::cnstr_get(x_394, 1);
lean::inc(x_396);
lean::dec(x_394);
x_397 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_395, x_393, x_2, x_396);
lean::dec(x_2);
lean::dec(x_393);
lean::dec(x_395);
x_398 = lean::cnstr_get(x_397, 0);
lean::inc(x_398);
x_399 = lean::cnstr_get(x_397, 1);
lean::inc(x_399);
lean::dec(x_397);
x_400 = !lean::is_exclusive(x_398);
if (x_400 == 0)
{
obj* x_401; obj* x_402; obj* x_403; 
x_401 = lean::cnstr_get(x_398, 0);
x_402 = lean::cnstr_get(x_398, 1);
lean::cnstr_set(x_1, 1, x_401);
x_403 = l_Lean_IR_reshape(x_402, x_1);
lean::cnstr_set(x_398, 1, x_399);
lean::cnstr_set(x_398, 0, x_403);
return x_398;
}
else
{
obj* x_404; obj* x_405; obj* x_406; obj* x_407; 
x_404 = lean::cnstr_get(x_398, 0);
x_405 = lean::cnstr_get(x_398, 1);
lean::inc(x_405);
lean::inc(x_404);
lean::dec(x_398);
lean::cnstr_set(x_1, 1, x_404);
x_406 = l_Lean_IR_reshape(x_405, x_1);
x_407 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_407, 0, x_406);
lean::cnstr_set(x_407, 1, x_399);
return x_407;
}
}
else
{
obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; 
x_408 = lean::cnstr_get(x_1, 0);
x_409 = lean::cnstr_get(x_1, 1);
lean::inc(x_409);
lean::inc(x_408);
lean::dec(x_1);
x_410 = l_Lean_IR_ExplicitBoxing_getJPParams(x_408, x_2, x_3);
x_411 = lean::cnstr_get(x_410, 0);
lean::inc(x_411);
x_412 = lean::cnstr_get(x_410, 1);
lean::inc(x_412);
lean::dec(x_410);
x_413 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_411, x_409, x_2, x_412);
lean::dec(x_2);
lean::dec(x_409);
lean::dec(x_411);
x_414 = lean::cnstr_get(x_413, 0);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_413, 1);
lean::inc(x_415);
lean::dec(x_413);
x_416 = lean::cnstr_get(x_414, 0);
lean::inc(x_416);
x_417 = lean::cnstr_get(x_414, 1);
lean::inc(x_417);
if (lean::is_exclusive(x_414)) {
 lean::cnstr_release(x_414, 0);
 lean::cnstr_release(x_414, 1);
 x_418 = x_414;
} else {
 lean::dec_ref(x_414);
 x_418 = lean::box(0);
}
x_419 = lean::alloc_cnstr(12, 2, 0);
lean::cnstr_set(x_419, 0, x_408);
lean::cnstr_set(x_419, 1, x_416);
x_420 = l_Lean_IR_reshape(x_417, x_419);
if (lean::is_scalar(x_418)) {
 x_421 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_421 = x_418;
}
lean::cnstr_set(x_421, 0, x_420);
lean::cnstr_set(x_421, 1, x_415);
return x_421;
}
}
default: 
{
obj* x_422; 
lean::dec(x_2);
x_422 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_422, 0, x_1);
lean::cnstr_set(x_422, 1, x_3);
return x_422;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_ExplicitBoxing_visitFnBody(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::array_fget(x_5, x_4);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = x_11;
x_13 = lean::array_fset(x_5, x_4, x_12);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
if (lean::obj_tag(x_10) == 0)
{
obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_18 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*3);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
x_20 = lean::mk_nat_obj(0u);
lean::inc(x_10);
x_21 = l_Lean_IR_MaxIndex_collectDecl___main(x_10, x_20);
x_22 = lean::nat_add(x_21, x_14);
lean::dec(x_21);
lean::inc(x_3);
x_23 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_17, x_17, x_20, x_3);
lean::inc(x_1);
lean::inc(x_2);
x_24 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_2);
lean::cnstr_set(x_24, 2, x_1);
lean::cnstr_set_scalar(x_24, sizeof(void*)*3, x_18);
x_25 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_19, x_24, x_22);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_27, 0, x_16);
lean::cnstr_set(x_27, 1, x_17);
lean::cnstr_set(x_27, 2, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*3, x_18);
x_28 = x_27;
x_29 = lean::array_fset(x_13, x_4, x_28);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_29;
goto _start;
}
else
{
obj* x_31; obj* x_32; 
lean::inc(x_10);
x_31 = x_10;
x_32 = lean::array_fset(x_13, x_4, x_31);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_32;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExplicitBoxing_run(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_2);
x_6 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_IR_explicitBoxing(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_Lean_IR_ExplicitBoxing_run(x_6, x_1);
lean::cnstr_set(x_4, 0, x_7);
return x_4;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_run(x_8, x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_4, 0);
x_14 = lean::cnstr_get(x_4, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_4);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_Lean_IR_explicitBoxing___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_explicitBoxing(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* initialize_init_control_estate(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_externattr(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_freevars(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_boxing(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_estate(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_externattr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (io_result_is_error(w)) return w;
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1();
lean::mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "mkBoxedName"), 1, l_Lean_IR_ExplicitBoxing_mkBoxedName);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "requiresBoxedVersion"), 2, l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean::mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "mkBoxedVersionAux"), 2, l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "mkBoxedVersion"), 1, l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "addBoxedVersions"), 2, l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "addBoxedVersion"), 2, lean::ir::add_boxed_version_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getScrutineeType"), 1, l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "eqvTypes"), 2, l_Lean_IR_ExplicitBoxing_eqvTypes___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "mkFresh"), 1, l_Lean_IR_ExplicitBoxing_mkFresh___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getEnv"), 2, l_Lean_IR_ExplicitBoxing_getEnv___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getLocalContext"), 2, l_Lean_IR_ExplicitBoxing_getLocalContext___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getResultType"), 2, l_Lean_IR_ExplicitBoxing_getResultType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getVarType"), 3, l_Lean_IR_ExplicitBoxing_getVarType___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getJPParams"), 3, l_Lean_IR_ExplicitBoxing_getJPParams___boxed);
l_Lean_IR_ExplicitBoxing_getDecl___closed__1 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1();
lean::mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "getDecl"), 3, l_Lean_IR_ExplicitBoxing_getDecl___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "withParams"), 1, l_Lean_IR_ExplicitBoxing_withParams);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "withVDecl"), 1, l_Lean_IR_ExplicitBoxing_withVDecl);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "withJDecl"), 1, l_Lean_IR_ExplicitBoxing_withJDecl);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "mkCast"), 2, l_Lean_IR_ExplicitBoxing_mkCast___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "castVarIfNeeded"), 5, l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "castArgIfNeeded"), 5, l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "castArgsIfNeededAux"), 4, l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "castArgsIfNeeded"), 5, l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "boxArgsIfNeeded"), 4, l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "unboxResultIfNeeded"), 6, l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "castResultIfNeeded"), 7, l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "visitVDeclExpr"), 6, l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "visitFnBody"), 3, l_Lean_IR_ExplicitBoxing_visitFnBody);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "ExplicitBoxing"), "run"), 2, l_Lean_IR_ExplicitBoxing_run);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "IR"), "explicitBoxing"), 3, l_Lean_IR_explicitBoxing___boxed);
return w;
}
