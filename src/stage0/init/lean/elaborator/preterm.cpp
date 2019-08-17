// Lean compiler output
// Module: init.lean.elaborator.preterm
// Imports: init.lean.elaborator.basic
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
extern obj* l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
obj* l_Lean_mkPreTypeAscription___closed__3;
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_Lean_addBuiltinPreTermElab(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_convertSorry(obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__3;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__5;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_Lean_Syntax_getKind___rarg(obj*);
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertHole(obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_builtinPreTermElabTable;
obj* l_Lean_Elab_convertType___rarg(obj*);
obj* l_Lean_Elab_toLevel___main___closed__4;
obj* l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
obj* l_Lean_Elab_convertSorry___rarg___closed__3;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
obj* l_Lean_Elab_convertHole___rarg(obj*);
extern obj* l_Lean_AttributeImpl_inhabited___closed__5;
obj* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3;
extern obj* l_Lean_Parser_Level_max___elambda__1___closed__1;
obj* l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
obj* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(obj*, obj*, obj*);
extern obj* l_Lean_addBuiltinTermElab___closed__2;
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
obj* l_Lean_mkBuiltinPreTermElabTable___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2;
obj* l_Lean_Elab_convertProp___rarg(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_2__setPos___closed__1;
obj* l_Lean_Elab_logError___rarg(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
extern "C" obj* level_mk_mvar(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__7;
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Elab_convertSort___boxed(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
obj* l_Lean_mkPreTypeAscriptionIfSome(obj*, obj*);
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_Lean_Elab_convertType(obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_mkPreTypeAscription___closed__1;
extern obj* l_Lean_mkInitAttr___lambda__1___closed__1;
extern obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1;
extern obj* l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__4;
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkPreTypeAscription___closed__2;
obj* l_Lean_Elab_toLevel___main(obj*, obj*, obj*);
obj* l_Lean_Elab_toPreTerm___closed__2;
obj* l_Lean_Elab_toLevel___boxed(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinPreTermElab___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__1;
obj* l_Lean_Level_ofNat___main(obj*);
obj* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_1__dummy___closed__1;
obj* l_IO_Prim_Ref_get___boxed(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
obj* l_Lean_declareBuiltinPreTermElab___closed__1;
obj* l_mkHashMap___at_Lean_mkBuiltinPreTermElabTable___spec__1(obj*);
obj* l_Lean_Elab_convertHole(obj*, obj*);
extern obj* l_Lean_AttributeImpl_inhabited___closed__4;
obj* l_Lean_oldElaborateAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_1__dummy;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__1;
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr(obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Elab_convertSort(obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_Elab_toPreTerm___closed__1;
extern "C" obj* lean_old_elaborate(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getArg___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_toLevel___main___closed__2;
extern obj* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
extern obj* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__3;
obj* l_Lean_Elab_convertSortApp(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern obj* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_convertHole___rarg___closed__1;
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
uint8 l_Lean_Syntax_isOfKind___rarg(obj*, obj*);
obj* l_Lean_Elab_convertHole___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
extern obj* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(obj*, obj*);
obj* l_Lean_Syntax_getArgs___rarg(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_mkPreTypeAscription(obj*, obj*);
extern obj* l_Lean_addBuiltinTermElab___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
obj* l___private_init_lean_elaborator_preterm_1__dummy___closed__2;
obj* l_Lean_Elab_getUniverses___rarg(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(obj*, obj*, obj*, uint8, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertProp(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2;
uint8 l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(obj*, obj*);
extern obj* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
extern obj* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
obj* l_Lean_Elab_convertSort___rarg(obj*);
obj* l_Lean_addBuiltinPreTermElab___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(obj*, obj*);
extern "C" obj* level_mk_imax(obj*, obj*);
obj* l_Lean_syntaxNodeKindOfAttrParam(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__6;
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
uint8 l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_2__setPos(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertType(obj*);
extern obj* l_Lean_Level_one___closed__1;
obj* l_Lean_mkAsIs___closed__2;
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(obj*, obj*, obj*);
obj* l_Lean_Elab_convertSorry___rarg___closed__2;
extern "C" obj* lean_expr_mk_mvar(obj*);
obj* l_Lean_Elab_toPreTerm___closed__3;
extern "C" obj* level_mk_param(obj*);
extern obj* l_Lean_Parser_Term_app___elambda__1___closed__2;
obj* l_Lean_Elab_convertArrow___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_convertArrow(obj*, obj*, obj*);
extern "C" obj* level_mk_succ(obj*);
obj* l_Lean_mkAsIs___closed__1;
extern obj* l_System_FilePath_dirName___closed__1;
obj* l_Lean_Elab_toLevel___main___closed__1;
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_Expr_mkAnnotation___closed__1;
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1;
obj* l_Lean_Syntax_getIdAt___rarg(obj*, obj*);
obj* l_Lean_Elab_convertSorry___boxed(obj*, obj*);
obj* l_Lean_ConstantInfo_type(obj*);
obj* l_Lean_Expr_mkAnnotation(obj*, obj*);
obj* l_Lean_mkBuiltinPreTermElabTable(obj*);
extern "C" obj* lean_environment_find(obj*, obj*);
obj* l_Lean_Elab_convertSorry___rarg___closed__4;
obj* l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
extern obj* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
obj* l_Lean_Elab_toPreTerm(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(obj*, obj*);
obj* l_Lean_Level_addOffsetAux___main(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Elab_convertSorry___rarg(obj*);
obj* l_Lean_Elab_toLevel(obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1;
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_convertType___boxed(obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp(obj*);
extern obj* l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_nameToExprAux___main___closed__4;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___regBuiltinTermElab_Lean_Elab_convertArrow(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSort(obj*);
obj* l_Lean_Syntax_toNat___rarg(obj*);
obj* l_Lean_Syntax_getPos___rarg(obj*);
extern obj* l_Lean_Parser_Level_imax___elambda__1___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2;
obj* l_Lean_Elab_convertProp(obj*, obj*);
obj* l_Lean_Elab_getScope___rarg(obj*);
obj* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(obj*, obj*, obj*);
obj* l_Lean_Elab_convertProp___boxed(obj*, obj*);
obj* l_Lean_FileMap_toPosition(obj*, obj*);
obj* l_Lean_declareBuiltinElab(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_logErrorAndThrow___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_convertSorry(obj*, obj*);
obj* l_Lean_Elab_convertSortApp___boxed(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2;
obj* l_Lean_Elab_logMessage(obj*, obj*, obj*);
obj* l_Lean_Elab_toLevel___main___closed__3;
obj* l_Lean_Elab_toLevel___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_oldElaborate(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_2__setPos___closed__3;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(obj*, obj*);
obj* l_Lean_Expr_mkAnnotation___closed__2;
obj* l_Lean_Elab_convertSorry___rarg___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_mkAsIs(obj*);
obj* l_Lean_Elab_mkFreshName___rarg(obj*);
obj* l_Lean_Elab_convertType___rarg___closed__1;
extern obj* l_Lean_exprIsInhabited___closed__1;
extern "C" obj* level_mk_max(obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
obj* l___private_init_lean_elaborator_preterm_2__setPos___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3;
obj* l_Lean_declareBuiltinPreTermElab(obj*, obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Elab_toPreTerm___closed__4;
obj* l_Lean_oldElaborateAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean_old_elaborate(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_mkHashMap___at_Lean_mkBuiltinPreTermElabTable___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_mkBuiltinPreTermElabTable___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_Lean_mkBuiltinPreTermElabTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkBuiltinPreTermElabTable___closed__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8 l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(obj* x_1, obj* x_2) {
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
x_6 = lean_name_dec_eq(x_4, x_1);
if (x_6 == 0)
{
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
uint8 l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::array_get_size(x_1);
x_7 = lean_name_hash_usize(x_4);
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
obj* x_15; obj* x_16; obj* x_17; obj* x_18; usize x_19; usize x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; usize x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::array_get_size(x_1);
x_19 = lean_name_hash_usize(x_15);
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
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::array_fget(x_2, x_1);
x_7 = lean::box(0);
x_8 = lean::array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean_name_dec_eq(x_5, x_1);
if (x_8 == 0)
{
obj* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_1, x_2, x_7);
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
x_13 = lean_name_dec_eq(x_10, x_1);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = lean_name_hash_usize(x_2);
x_9 = lean::usize_modn(x_8, x_7);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::array_uget(x_6, x_11);
x_13 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_2, x_3, x_12);
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
x_27 = lean_name_hash_usize(x_2);
x_28 = lean::usize_modn(x_27, x_26);
x_29 = lean::box_size_t(x_28);
x_30 = lean::unbox_size_t(x_29);
x_31 = lean::array_uget(x_25, x_30);
x_32 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(x_2, x_3, x_31);
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
obj* l_Lean_addBuiltinPreTermElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_builtinPreTermElabTable;
x_6 = lean::io_ref_get(x_5, x_4);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_8, x_1);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::box(0);
lean::cnstr_set(x_6, 0, x_10);
x_11 = lean::io_ref_get(x_5, x_6);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
lean::cnstr_set(x_11, 0, x_10);
x_14 = lean::io_ref_reset(x_5, x_11);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_14, 0);
lean::dec(x_16);
lean::cnstr_set(x_14, 0, x_10);
x_17 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_13, x_1, x_3);
x_18 = lean::io_ref_set(x_5, x_17, x_14);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_13, x_1, x_3);
x_22 = lean::io_ref_set(x_5, x_21, x_20);
return x_22;
}
}
else
{
uint8 x_23; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_1);
x_23 = !lean::is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_14, 0);
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_14);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_11, 0);
x_28 = lean::cnstr_get(x_11, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_11);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::io_ref_reset(x_5, x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_32 = x_30;
} else {
 lean::dec_ref(x_30);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_10);
lean::cnstr_set(x_33, 1, x_31);
x_34 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_27, x_1, x_3);
x_35 = lean::io_ref_set(x_5, x_34, x_33);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_30, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_30, 1);
lean::inc(x_37);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_38 = x_30;
} else {
 lean::dec_ref(x_30);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_3);
lean::dec(x_1);
x_40 = !lean::is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_11, 0);
x_42 = lean::cnstr_get(x_11, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_11);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_3);
x_44 = l_System_FilePath_dirName___closed__1;
x_45 = l_Lean_Name_toStringWithSep___main(x_44, x_1);
x_46 = l_Lean_addBuiltinTermElab___closed__1;
x_47 = lean::string_append(x_46, x_45);
lean::dec(x_45);
x_48 = l_Lean_addBuiltinTermElab___closed__2;
x_49 = lean::string_append(x_47, x_48);
lean::cnstr_set_tag(x_6, 1);
lean::cnstr_set(x_6, 0, x_49);
return x_6;
}
}
else
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = lean::cnstr_get(x_6, 0);
x_51 = lean::cnstr_get(x_6, 1);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_6);
x_52 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_50, x_1);
lean::dec(x_50);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
x_55 = lean::io_ref_get(x_5, x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_55, 1);
lean::inc(x_57);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_58 = x_55;
} else {
 lean::dec_ref(x_55);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_53);
lean::cnstr_set(x_59, 1, x_57);
x_60 = lean::io_ref_reset(x_5, x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_62 = x_60;
} else {
 lean::dec_ref(x_60);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_53);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(x_56, x_1, x_3);
x_65 = lean::io_ref_set(x_5, x_64, x_63);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_56);
lean::dec(x_3);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_60, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_60, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_68 = x_60;
} else {
 lean::dec_ref(x_60);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_3);
lean::dec(x_1);
x_70 = lean::cnstr_get(x_55, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_55, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_72 = x_55;
} else {
 lean::dec_ref(x_55);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_3);
x_74 = l_System_FilePath_dirName___closed__1;
x_75 = l_Lean_Name_toStringWithSep___main(x_74, x_1);
x_76 = l_Lean_addBuiltinTermElab___closed__1;
x_77 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_78 = l_Lean_addBuiltinTermElab___closed__2;
x_79 = lean::string_append(x_77, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_51);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_3);
lean::dec(x_1);
x_81 = !lean::is_exclusive(x_6);
if (x_81 == 0)
{
return x_6;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_6, 0);
x_83 = lean::cnstr_get(x_6, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_6);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_addBuiltinPreTermElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_addBuiltinPreTermElab(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_declareBuiltinPreTermElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("addBuiltinPreTermElab");
return x_1;
}
}
obj* _init_l_Lean_declareBuiltinPreTermElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_declareBuiltinPreTermElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_declareBuiltinPreTermElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_declareBuiltinPreTermElab___closed__2;
x_6 = l_Lean_declareBuiltinElab(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid attribute 'builtinPreTermElab', must be persistent");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected preterm elaborator type at '");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' `PreTermElab` expected");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("PreTermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
_start:
{
if (x_4 == 0)
{
uint8 x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::dec(x_7);
x_8 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_5, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_5, 0, x_14);
x_15 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean::inc(x_1);
x_16 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_15, x_3, x_5);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_29; obj* x_30; 
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_19 = x_16;
} else {
 lean::dec_ref(x_16);
 x_19 = lean::box(0);
}
lean::inc(x_18);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_14);
lean::cnstr_set(x_29, 1, x_18);
lean::inc(x_2);
lean::inc(x_1);
x_30 = lean_environment_find(x_1, x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_29);
lean::dec(x_19);
lean::dec(x_17);
lean::dec(x_2);
lean::dec(x_1);
x_31 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_18);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
lean::dec(x_30);
x_34 = l_Lean_ConstantInfo_type(x_33);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 4)
{
obj* x_35; obj* x_36; uint8 x_37; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::dec(x_34);
x_36 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
x_37 = lean_name_dec_eq(x_35, x_36);
lean::dec(x_35);
if (x_37 == 0)
{
lean::dec(x_29);
lean::dec(x_17);
lean::dec(x_1);
x_20 = x_14;
goto block_28;
}
else
{
obj* x_38; 
lean::dec(x_19);
lean::dec(x_18);
x_38 = l_Lean_declareBuiltinPreTermElab(x_1, x_17, x_2, x_29);
return x_38;
}
}
else
{
lean::dec(x_34);
lean::dec(x_29);
lean::dec(x_17);
lean::dec(x_1);
x_20 = x_14;
goto block_28;
}
}
block_28:
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_20);
x_21 = l_System_FilePath_dirName___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_2);
x_23 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_25 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
x_26 = lean::string_append(x_24, x_25);
if (lean::is_scalar(x_19)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_19;
 lean::cnstr_set_tag(x_27, 1);
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
return x_27;
}
}
else
{
uint8 x_39; 
lean::dec(x_2);
lean::dec(x_1);
x_39 = !lean::is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_16, 0);
x_41 = lean::cnstr_get(x_16, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_16);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_43 = lean::cnstr_get(x_5, 1);
lean::inc(x_43);
lean::dec(x_5);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
x_46 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean::inc(x_1);
x_47 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_46, x_3, x_45);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_60; obj* x_61; 
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_47, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_50 = x_47;
} else {
 lean::dec_ref(x_47);
 x_50 = lean::box(0);
}
lean::inc(x_49);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_44);
lean::cnstr_set(x_60, 1, x_49);
lean::inc(x_2);
lean::inc(x_1);
x_61 = lean_environment_find(x_1, x_2);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_60);
lean::dec(x_50);
lean::dec(x_48);
lean::dec(x_2);
lean::dec(x_1);
x_62 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_49);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
x_65 = l_Lean_ConstantInfo_type(x_64);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 4)
{
obj* x_66; obj* x_67; uint8 x_68; 
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
lean::dec(x_65);
x_67 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
x_68 = lean_name_dec_eq(x_66, x_67);
lean::dec(x_66);
if (x_68 == 0)
{
lean::dec(x_60);
lean::dec(x_48);
lean::dec(x_1);
x_51 = x_44;
goto block_59;
}
else
{
obj* x_69; 
lean::dec(x_50);
lean::dec(x_49);
x_69 = l_Lean_declareBuiltinPreTermElab(x_1, x_48, x_2, x_60);
return x_69;
}
}
else
{
lean::dec(x_65);
lean::dec(x_60);
lean::dec(x_48);
lean::dec(x_1);
x_51 = x_44;
goto block_59;
}
}
block_59:
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_51);
x_52 = l_System_FilePath_dirName___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_2);
x_54 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
x_55 = lean::string_append(x_54, x_53);
lean::dec(x_53);
x_56 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3;
x_57 = lean::string_append(x_55, x_56);
if (lean::is_scalar(x_50)) {
 x_58 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_58 = x_50;
 lean::cnstr_set_tag(x_58, 1);
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_49);
return x_58;
}
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_2);
lean::dec(x_1);
x_70 = lean::cnstr_get(x_47, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_47, 1);
lean::inc(x_71);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_72 = x_47;
} else {
 lean::dec_ref(x_47);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_71);
return x_73;
}
}
}
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinPreTermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Builtin preterm conversion elaborator, we use it to interface with the Lean3 elaborator");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinPreTermElabAttr___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_1 = l_Lean_registerBuiltinPreTermElabAttr___closed__2;
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinPreTermElabAttr___closed__6;
x_4 = l_Lean_registerBuiltinPreTermElabAttr___closed__3;
x_5 = l_Lean_registerBuiltinPreTermElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_4);
lean::cnstr_set(x_9, 4, x_5);
lean::cnstr_set(x_9, 5, x_6);
lean::cnstr_set(x_9, 6, x_7);
lean::cnstr_set(x_9, 7, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
obj* l_Lean_registerBuiltinPreTermElabAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_registerBuiltinPreTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_registerBuiltinPreTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* _init_l_Lean_Expr_mkAnnotation___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("annotation");
return x_1;
}
}
obj* _init_l_Lean_Expr_mkAnnotation___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Expr_mkAnnotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_mkAnnotation(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = l_Lean_Expr_mkAnnotation___closed__2;
x_5 = l_Lean_KVMap_setName(x_3, x_4, x_1);
x_6 = lean_expr_mk_mdata(x_5, x_2);
return x_6;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_elaborator_preterm_1__dummy___closed__1;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_1__dummy() {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_elaborator_preterm_1__dummy___closed__2;
return x_1;
}
}
obj* _init_l_Lean_mkAsIs___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("as_is");
return x_1;
}
}
obj* _init_l_Lean_mkAsIs___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkAsIs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkAsIs(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkAsIs___closed__2;
x_3 = l_Lean_Expr_mkAnnotation(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkPreTypeAscription___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("typedExpr");
return x_1;
}
}
obj* _init_l_Lean_mkPreTypeAscription___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkPreTypeAscription___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_mkPreTypeAscription___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkPreTypeAscription___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
obj* l_Lean_mkPreTypeAscription(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_mkPreTypeAscription___closed__3;
x_4 = lean_expr_mk_app(x_3, x_2);
x_5 = lean_expr_mk_app(x_4, x_1);
return x_5;
}
}
obj* l_Lean_mkPreTypeAscriptionIfSome(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_4 = l_Lean_mkPreTypeAscription(x_1, x_3);
return x_4;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_4);
return x_6;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_16 = l_Lean_Elab_toLevel___main(x_13, x_5, x_6);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = level_mk_imax(x_4, x_18);
x_20 = lean::box(0);
lean::cnstr_set(x_16, 0, x_20);
x_3 = x_15;
x_4 = x_19;
x_6 = x_16;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_16);
x_24 = level_mk_imax(x_4, x_22);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
x_3 = x_15;
x_4 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8 x_28; 
lean::dec(x_15);
lean::dec(x_4);
x_28 = !lean::is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_16, 0);
x_30 = lean::cnstr_get(x_16, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_16);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_4);
return x_6;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_16 = l_Lean_Elab_toLevel___main(x_13, x_5, x_6);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = level_mk_max(x_4, x_18);
x_20 = lean::box(0);
lean::cnstr_set(x_16, 0, x_20);
x_3 = x_15;
x_4 = x_19;
x_6 = x_16;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_16);
x_24 = level_mk_max(x_4, x_22);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
x_3 = x_15;
x_4 = x_24;
x_6 = x_26;
goto _start;
}
}
else
{
uint8 x_28; 
lean::dec(x_15);
lean::dec(x_4);
x_28 = !lean::is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_16, 0);
x_30 = lean::cnstr_get(x_16, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_16);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
obj* _init_l_Lean_Elab_toLevel___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected universe level syntax");
return x_1;
}
}
obj* _init_l_Lean_Elab_toLevel___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_toLevel___main___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_toLevel___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown universe variable '");
return x_1;
}
}
obj* _init_l_Lean_Elab_toLevel___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = level_mk_mvar(x_1);
return x_2;
}
}
obj* l_Lean_Elab_toLevel___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = l_Lean_Syntax_getKind___rarg(x_1);
x_5 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_8 = lean_name_dec_eq(x_4, x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_10 = lean_name_dec_eq(x_4, x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
x_12 = lean_name_dec_eq(x_4, x_11);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = l_Lean_Parser_Level_num___elambda__1___rarg___closed__2;
x_14 = lean_name_dec_eq(x_4, x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = l_Lean_Parser_Level_ident___elambda__1___rarg___closed__1;
x_16 = lean_name_dec_eq(x_4, x_15);
if (x_16 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_18 = lean_name_dec_eq(x_4, x_17);
lean::dec(x_4);
if (x_18 == 0)
{
uint8 x_19; 
lean::dec(x_1);
x_19 = !lean::is_exclusive(x_3);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_3, 0);
lean::dec(x_20);
x_21 = l_Lean_Elab_toLevel___main___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_21);
return x_3;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
lean::dec(x_3);
x_23 = l_Lean_Elab_toLevel___main___closed__2;
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::mk_nat_obj(0u);
x_26 = l_Lean_Syntax_getArg___rarg(x_1, x_25);
x_27 = l_Lean_Elab_toLevel___main(x_26, x_2, x_3);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = lean::mk_nat_obj(2u);
x_31 = l_Lean_Syntax_getArg___rarg(x_1, x_30);
lean::dec(x_1);
x_32 = l_Lean_Syntax_toNat___rarg(x_31);
lean::dec(x_31);
x_33 = l_Lean_Level_addOffsetAux___main(x_32, x_29);
lean::cnstr_set(x_27, 0, x_33);
return x_27;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_34 = lean::cnstr_get(x_27, 0);
x_35 = lean::cnstr_get(x_27, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_27);
x_36 = lean::mk_nat_obj(2u);
x_37 = l_Lean_Syntax_getArg___rarg(x_1, x_36);
lean::dec(x_1);
x_38 = l_Lean_Syntax_toNat___rarg(x_37);
lean::dec(x_37);
x_39 = l_Lean_Level_addOffsetAux___main(x_38, x_34);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_35);
return x_40;
}
}
else
{
uint8 x_41; 
lean::dec(x_1);
x_41 = !lean::is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = lean::cnstr_get(x_27, 0);
x_43 = lean::cnstr_get(x_27, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_27);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_4);
x_45 = lean::mk_nat_obj(0u);
x_46 = l_Lean_Syntax_getIdAt___rarg(x_1, x_45);
x_47 = l_Lean_Elab_getUniverses___rarg(x_3);
if (lean::obj_tag(x_47) == 0)
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_47);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; uint8 x_52; 
x_49 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
x_51 = lean::box(0);
lean::inc(x_50);
lean::cnstr_set(x_47, 0, x_51);
x_52 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_46, x_49);
lean::dec(x_49);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_50);
x_53 = l_System_FilePath_dirName___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_46);
x_55 = l_Lean_Elab_toLevel___main___closed__3;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_56, x_57);
x_59 = l_Lean_Elab_logError___rarg(x_1, x_58, x_2, x_47);
lean::dec(x_1);
if (lean::obj_tag(x_59) == 0)
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_59);
if (x_60 == 0)
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_59, 0);
lean::dec(x_61);
x_62 = l_Lean_Elab_toLevel___main___closed__4;
lean::cnstr_set(x_59, 0, x_62);
return x_59;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
lean::dec(x_59);
x_64 = l_Lean_Elab_toLevel___main___closed__4;
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8 x_66; 
x_66 = !lean::is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = lean::cnstr_get(x_59, 0);
x_68 = lean::cnstr_get(x_59, 1);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_59);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_47);
lean::dec(x_1);
x_70 = level_mk_param(x_46);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_50);
return x_71;
}
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; uint8 x_76; 
x_72 = lean::cnstr_get(x_47, 0);
x_73 = lean::cnstr_get(x_47, 1);
lean::inc(x_73);
lean::inc(x_72);
lean::dec(x_47);
x_74 = lean::box(0);
lean::inc(x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
x_76 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_46, x_72);
lean::dec(x_72);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_73);
x_77 = l_System_FilePath_dirName___closed__1;
x_78 = l_Lean_Name_toStringWithSep___main(x_77, x_46);
x_79 = l_Lean_Elab_toLevel___main___closed__3;
x_80 = lean::string_append(x_79, x_78);
lean::dec(x_78);
x_81 = l_Char_HasRepr___closed__1;
x_82 = lean::string_append(x_80, x_81);
x_83 = l_Lean_Elab_logError___rarg(x_1, x_82, x_2, x_75);
lean::dec(x_1);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_85 = x_83;
} else {
 lean::dec_ref(x_83);
 x_85 = lean::box(0);
}
x_86 = l_Lean_Elab_toLevel___main___closed__4;
if (lean::is_scalar(x_85)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_85;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get(x_83, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_83, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_90 = x_83;
} else {
 lean::dec_ref(x_83);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_89);
return x_91;
}
}
else
{
obj* x_92; obj* x_93; 
lean::dec(x_75);
lean::dec(x_1);
x_92 = level_mk_param(x_46);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
uint8 x_94; 
lean::dec(x_46);
lean::dec(x_1);
x_94 = !lean::is_exclusive(x_47);
if (x_94 == 0)
{
return x_47;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
x_95 = lean::cnstr_get(x_47, 0);
x_96 = lean::cnstr_get(x_47, 1);
lean::inc(x_96);
lean::inc(x_95);
lean::dec(x_47);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8 x_98; 
lean::dec(x_4);
x_98 = !lean::is_exclusive(x_3);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_99 = lean::cnstr_get(x_3, 0);
lean::dec(x_99);
x_100 = lean::mk_nat_obj(0u);
x_101 = l_Lean_Syntax_getArg___rarg(x_1, x_100);
lean::dec(x_1);
x_102 = l_Lean_Syntax_toNat___rarg(x_101);
lean::dec(x_101);
x_103 = l_Lean_Level_ofNat___main(x_102);
lean::dec(x_102);
lean::cnstr_set(x_3, 0, x_103);
return x_3;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_3, 1);
lean::inc(x_104);
lean::dec(x_3);
x_105 = lean::mk_nat_obj(0u);
x_106 = l_Lean_Syntax_getArg___rarg(x_1, x_105);
lean::dec(x_1);
x_107 = l_Lean_Syntax_toNat___rarg(x_106);
lean::dec(x_106);
x_108 = l_Lean_Level_ofNat___main(x_107);
lean::dec(x_107);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_104);
return x_109;
}
}
}
else
{
uint8 x_110; 
lean::dec(x_4);
lean::dec(x_1);
x_110 = !lean::is_exclusive(x_3);
if (x_110 == 0)
{
obj* x_111; obj* x_112; 
x_111 = lean::cnstr_get(x_3, 0);
lean::dec(x_111);
x_112 = l_Lean_Elab_toLevel___main___closed__4;
lean::cnstr_set(x_3, 0, x_112);
return x_3;
}
else
{
obj* x_113; obj* x_114; obj* x_115; 
x_113 = lean::cnstr_get(x_3, 1);
lean::inc(x_113);
lean::dec(x_3);
x_114 = l_Lean_Elab_toLevel___main___closed__4;
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
lean::dec(x_4);
x_116 = lean::mk_nat_obj(1u);
x_117 = l_Lean_Syntax_getArg___rarg(x_1, x_116);
x_118 = l_Lean_Syntax_getArgs___rarg(x_117);
lean::dec(x_117);
x_119 = lean::box(0);
x_120 = lean::mk_nat_obj(0u);
x_121 = lean::array_get(x_119, x_118, x_120);
x_122 = l_Lean_Elab_toLevel___main(x_121, x_2, x_3);
if (lean::obj_tag(x_122) == 0)
{
uint8 x_123; 
x_123 = !lean::is_exclusive(x_122);
if (x_123 == 0)
{
obj* x_124; obj* x_125; obj* x_126; 
x_124 = lean::cnstr_get(x_122, 0);
x_125 = lean::box(0);
lean::cnstr_set(x_122, 0, x_125);
x_126 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_118, x_116, x_124, x_2, x_122);
lean::dec(x_118);
lean::dec(x_1);
return x_126;
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_127 = lean::cnstr_get(x_122, 0);
x_128 = lean::cnstr_get(x_122, 1);
lean::inc(x_128);
lean::inc(x_127);
lean::dec(x_122);
x_129 = lean::box(0);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_128);
x_131 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_118, x_116, x_127, x_2, x_130);
lean::dec(x_118);
lean::dec(x_1);
return x_131;
}
}
else
{
uint8 x_132; 
lean::dec(x_118);
lean::dec(x_1);
x_132 = !lean::is_exclusive(x_122);
if (x_132 == 0)
{
return x_122;
}
else
{
obj* x_133; obj* x_134; obj* x_135; 
x_133 = lean::cnstr_get(x_122, 0);
x_134 = lean::cnstr_get(x_122, 1);
lean::inc(x_134);
lean::inc(x_133);
lean::dec(x_122);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_4);
x_136 = lean::mk_nat_obj(1u);
x_137 = l_Lean_Syntax_getArg___rarg(x_1, x_136);
x_138 = l_Lean_Syntax_getArgs___rarg(x_137);
lean::dec(x_137);
x_139 = lean::box(0);
x_140 = lean::mk_nat_obj(0u);
x_141 = lean::array_get(x_139, x_138, x_140);
x_142 = l_Lean_Elab_toLevel___main(x_141, x_2, x_3);
if (lean::obj_tag(x_142) == 0)
{
uint8 x_143; 
x_143 = !lean::is_exclusive(x_142);
if (x_143 == 0)
{
obj* x_144; obj* x_145; obj* x_146; 
x_144 = lean::cnstr_get(x_142, 0);
x_145 = lean::box(0);
lean::cnstr_set(x_142, 0, x_145);
x_146 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_138, x_136, x_144, x_2, x_142);
lean::dec(x_138);
lean::dec(x_1);
return x_146;
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_147 = lean::cnstr_get(x_142, 0);
x_148 = lean::cnstr_get(x_142, 1);
lean::inc(x_148);
lean::inc(x_147);
lean::dec(x_142);
x_149 = lean::box(0);
x_150 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_148);
x_151 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_138, x_136, x_147, x_2, x_150);
lean::dec(x_138);
lean::dec(x_1);
return x_151;
}
}
else
{
uint8 x_152; 
lean::dec(x_138);
lean::dec(x_1);
x_152 = !lean::is_exclusive(x_142);
if (x_152 == 0)
{
return x_142;
}
else
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = lean::cnstr_get(x_142, 0);
x_154 = lean::cnstr_get(x_142, 1);
lean::inc(x_154);
lean::inc(x_153);
lean::dec(x_142);
x_155 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
obj* x_156; obj* x_157; 
lean::dec(x_4);
x_156 = lean::mk_nat_obj(1u);
x_157 = l_Lean_Syntax_getArg___rarg(x_1, x_156);
lean::dec(x_1);
x_1 = x_157;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_Elab_toLevel___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Elab_toLevel___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_toLevel___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_toLevel(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_toLevel___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elab_toLevel___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_toLevel(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("column");
return x_1;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_elaborator_preterm_2__setPos___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("row");
return x_1;
}
}
obj* _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_elaborator_preterm_2__setPos___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_elaborator_preterm_2__setPos(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_6 = l_Lean_Syntax_isOfKind___rarg(x_1, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean::obj_tag(x_9) == 0)
{
lean::cnstr_set(x_4, 0, x_2);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_3, 1);
x_12 = l_Lean_FileMap_toPosition(x_11, x_10);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_14 = lean::box(0);
x_15 = l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
x_16 = l_Lean_KVMap_setNat(x_14, x_15, x_13);
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
lean::dec(x_12);
x_18 = l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
x_19 = l_Lean_KVMap_setNat(x_16, x_18, x_17);
x_20 = lean_expr_mk_mdata(x_19, x_2);
lean::cnstr_set(x_4, 0, x_20);
return x_4;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_22 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::cnstr_get(x_3, 1);
x_26 = l_Lean_FileMap_toPosition(x_25, x_24);
lean::dec(x_24);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_28 = lean::box(0);
x_29 = l___private_init_lean_elaborator_preterm_2__setPos___closed__2;
x_30 = l_Lean_KVMap_setNat(x_28, x_29, x_27);
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
lean::dec(x_26);
x_32 = l___private_init_lean_elaborator_preterm_2__setPos___closed__4;
x_33 = l_Lean_KVMap_setNat(x_30, x_32, x_31);
x_34 = lean_expr_mk_mdata(x_33, x_2);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_21);
return x_35;
}
}
}
else
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_4);
if (x_36 == 0)
{
obj* x_37; 
x_37 = lean::cnstr_get(x_4, 0);
lean::dec(x_37);
lean::cnstr_set(x_4, 0, x_2);
return x_4;
}
else
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_4, 1);
lean::inc(x_38);
lean::dec(x_4);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_2);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
obj* l___private_init_lean_elaborator_preterm_2__setPos___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = lean_name_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
obj* x_9; 
lean::inc(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_5);
return x_9;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; usize x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean_name_hash_usize(x_2);
x_6 = lean::usize_modn(x_5, x_4);
lean::dec(x_4);
x_7 = lean::box_size_t(x_6);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean::array_uget(x_3, x_8);
x_10 = l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* _init_l_Lean_Elab_toPreTerm___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("`toPreTerm` failed, unexpected syntax");
return x_1;
}
}
obj* _init_l_Lean_Elab_toPreTerm___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_toPreTerm___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_toPreTerm___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_builtinPreTermElabTable;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_Prim_Ref_get___boxed), 3, 2);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_toPreTerm___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("`toPreTerm` failed, no support for syntax '");
return x_1;
}
}
obj* l_Lean_Elab_toPreTerm(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::box(0);
lean::cnstr_set(x_3, 0, x_7);
x_8 = l_Lean_Elab_toPreTerm___closed__3;
x_9 = l_Lean_Elab_runIOUnsafe___rarg(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::cnstr_set(x_9, 0, x_7);
x_12 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_11, x_4);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_4);
x_15 = l_Lean_Elab_toPreTerm___closed__4;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_17 = l_Char_HasRepr___closed__1;
x_18 = lean::string_append(x_16, x_17);
x_19 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_18, x_2, x_9);
lean::dec(x_2);
lean::dec(x_1);
return x_19;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_4);
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
lean::inc(x_2);
lean::inc(x_1);
x_21 = lean::apply_3(x_20, x_1, x_2, x_9);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_7);
x_24 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_23, x_2, x_21);
lean::dec(x_2);
lean::dec(x_1);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_21);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_25, x_2, x_27);
lean::dec(x_2);
lean::dec(x_1);
return x_28;
}
}
else
{
uint8 x_29; 
lean::dec(x_2);
lean::dec(x_1);
x_29 = !lean::is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_21, 0);
x_31 = lean::cnstr_get(x_21, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_21);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_9, 0);
x_34 = lean::cnstr_get(x_9, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_9);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_7);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_33, x_4);
lean::dec(x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_37 = l_System_FilePath_dirName___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_4);
x_39 = l_Lean_Elab_toPreTerm___closed__4;
x_40 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_40, x_41);
x_43 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_42, x_2, x_35);
lean::dec(x_2);
lean::dec(x_1);
return x_43;
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_4);
x_44 = lean::cnstr_get(x_36, 0);
lean::inc(x_44);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
x_45 = lean::apply_3(x_44, x_1, x_2, x_35);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_48 = x_45;
} else {
 lean::dec_ref(x_45);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_7);
lean::cnstr_set(x_49, 1, x_47);
x_50 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_46, x_2, x_49);
lean::dec(x_2);
lean::dec(x_1);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_2);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_45, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_45, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_53 = x_45;
} else {
 lean::dec_ref(x_45);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
}
else
{
uint8 x_55; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_55 = !lean::is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_9, 0);
x_57 = lean::cnstr_get(x_9, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_9);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_3, 1);
lean::inc(x_59);
lean::dec(x_3);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_toPreTerm___closed__3;
x_63 = l_Lean_Elab_runIOUnsafe___rarg(x_62, x_2, x_61);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_66 = x_63;
} else {
 lean::dec_ref(x_63);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_60);
lean::cnstr_set(x_67, 1, x_65);
x_68 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_64, x_4);
lean::dec(x_64);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = l_System_FilePath_dirName___closed__1;
x_70 = l_Lean_Name_toStringWithSep___main(x_69, x_4);
x_71 = l_Lean_Elab_toPreTerm___closed__4;
x_72 = lean::string_append(x_71, x_70);
lean::dec(x_70);
x_73 = l_Char_HasRepr___closed__1;
x_74 = lean::string_append(x_72, x_73);
x_75 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_74, x_2, x_67);
lean::dec(x_2);
lean::dec(x_1);
return x_75;
}
else
{
obj* x_76; obj* x_77; 
lean::dec(x_4);
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
lean::inc(x_2);
lean::inc(x_1);
x_77 = lean::apply_3(x_76, x_1, x_2, x_67);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_77, 1);
lean::inc(x_79);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_80 = x_77;
} else {
 lean::dec_ref(x_77);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_60);
lean::cnstr_set(x_81, 1, x_79);
x_82 = l___private_init_lean_elaborator_preterm_2__setPos(x_1, x_78, x_2, x_81);
lean::dec(x_2);
lean::dec(x_1);
return x_82;
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_2);
lean::dec(x_1);
x_83 = lean::cnstr_get(x_77, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_77, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_85 = x_77;
} else {
 lean::dec_ref(x_77);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
lean::cnstr_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_87 = lean::cnstr_get(x_63, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_63, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_89 = x_63;
} else {
 lean::dec_ref(x_63);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8 x_91; 
lean::dec(x_2);
lean::dec(x_1);
x_91 = !lean::is_exclusive(x_3);
if (x_91 == 0)
{
obj* x_92; obj* x_93; 
x_92 = lean::cnstr_get(x_3, 0);
lean::dec(x_92);
x_93 = l_Lean_Elab_toPreTerm___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_93);
return x_3;
}
else
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_3, 1);
lean::inc(x_94);
lean::dec(x_3);
x_95 = l_Lean_Elab_toPreTerm___closed__2;
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_94);
return x_96;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Elab_convertType___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Level_one___closed__1;
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* l_Lean_Elab_convertType___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_Elab_convertType___rarg___closed__1;
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_Elab_convertType___rarg___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_convertType(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertType___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_convertType___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_convertType(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Elab");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertType");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertType___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertType(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_convertSort___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_exprIsInhabited___closed__1;
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_exprIsInhabited___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_convertSort(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertSort___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_convertSort___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_convertSort(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertSort");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertSort___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSort(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_convertProp___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_exprIsInhabited___closed__1;
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_exprIsInhabited___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_convertProp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertProp___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_convertProp___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_convertProp(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertProp");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertProp___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertProp(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_convertSortApp(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::array_get(x_5, x_4, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::array_get(x_5, x_4, x_8);
x_10 = l_Lean_Elab_toLevel___main(x_9, x_2, x_3);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_14 = l_Lean_Syntax_isOfKind___rarg(x_7, x_13);
lean::dec(x_7);
if (x_14 == 0)
{
obj* x_15; 
x_15 = lean_expr_mk_sort(x_12);
lean::cnstr_set(x_10, 0, x_15);
return x_10;
}
else
{
obj* x_16; obj* x_17; 
x_16 = level_mk_succ(x_12);
x_17 = lean_expr_mk_sort(x_16);
lean::cnstr_set(x_10, 0, x_17);
return x_10;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_18 = lean::cnstr_get(x_10, 0);
x_19 = lean::cnstr_get(x_10, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_10);
x_20 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_21 = l_Lean_Syntax_isOfKind___rarg(x_7, x_20);
lean::dec(x_7);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean_expr_mk_sort(x_18);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = level_mk_succ(x_18);
x_25 = lean_expr_mk_sort(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_19);
return x_26;
}
}
}
else
{
uint8 x_27; 
lean::dec(x_7);
x_27 = !lean::is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_10, 0);
x_29 = lean::cnstr_get(x_10, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_10);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
obj* l_Lean_Elab_convertSortApp___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_convertSortApp(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertSortApp");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertSortApp___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_convertArrow(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_mkFreshName___rarg(x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::box(0);
lean::cnstr_set(x_4, 0, x_8);
x_9 = lean::box(0);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::array_get(x_9, x_7, x_10);
lean::inc(x_2);
x_12 = l_Lean_Elab_toPreTerm(x_11, x_2, x_4);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_12, 0, x_8);
x_15 = lean::mk_nat_obj(2u);
x_16 = lean::array_get(x_9, x_7, x_15);
x_17 = l_Lean_Elab_toPreTerm(x_16, x_2, x_12);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = 0;
x_21 = lean_expr_mk_pi(x_6, x_20, x_14, x_19);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_17);
x_24 = 0;
x_25 = lean_expr_mk_pi(x_6, x_24, x_14, x_22);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8 x_27; 
lean::dec(x_14);
lean::dec(x_6);
x_27 = !lean::is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_17, 0);
x_29 = lean::cnstr_get(x_17, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_17);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_12, 0);
x_32 = lean::cnstr_get(x_12, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_12);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_8);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::mk_nat_obj(2u);
x_35 = lean::array_get(x_9, x_7, x_34);
x_36 = l_Lean_Elab_toPreTerm(x_35, x_2, x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; uint8 x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_39 = x_36;
} else {
 lean::dec_ref(x_36);
 x_39 = lean::box(0);
}
x_40 = 0;
x_41 = lean_expr_mk_pi(x_6, x_40, x_31, x_37);
if (lean::is_scalar(x_39)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_39;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_38);
return x_42;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_31);
lean::dec(x_6);
x_43 = lean::cnstr_get(x_36, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_36, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_45 = x_36;
} else {
 lean::dec_ref(x_36);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8 x_47; 
lean::dec(x_6);
lean::dec(x_2);
x_47 = !lean::is_exclusive(x_12);
if (x_47 == 0)
{
return x_12;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_12, 0);
x_49 = lean::cnstr_get(x_12, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_12);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_51 = lean::cnstr_get(x_4, 0);
x_52 = lean::cnstr_get(x_4, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_4);
x_53 = lean::cnstr_get(x_1, 1);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_52);
x_56 = lean::box(0);
x_57 = lean::mk_nat_obj(0u);
x_58 = lean::array_get(x_56, x_53, x_57);
lean::inc(x_2);
x_59 = l_Lean_Elab_toPreTerm(x_58, x_2, x_55);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_59, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_62 = x_59;
} else {
 lean::dec_ref(x_59);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_54);
lean::cnstr_set(x_63, 1, x_61);
x_64 = lean::mk_nat_obj(2u);
x_65 = lean::array_get(x_56, x_53, x_64);
x_66 = l_Lean_Elab_toPreTerm(x_65, x_2, x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; obj* x_69; uint8 x_70; obj* x_71; obj* x_72; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 x_69 = x_66;
} else {
 lean::dec_ref(x_66);
 x_69 = lean::box(0);
}
x_70 = 0;
x_71 = lean_expr_mk_pi(x_51, x_70, x_60, x_67);
if (lean::is_scalar(x_69)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_69;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_68);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_60);
lean::dec(x_51);
x_73 = lean::cnstr_get(x_66, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_66, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 x_75 = x_66;
} else {
 lean::dec_ref(x_66);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_51);
lean::dec(x_2);
x_77 = lean::cnstr_get(x_59, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_59, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_79 = x_59;
} else {
 lean::dec_ref(x_59);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8 x_81; 
lean::dec(x_2);
x_81 = !lean::is_exclusive(x_4);
if (x_81 == 0)
{
return x_4;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_4, 0);
x_83 = lean::cnstr_get(x_4, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_4);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
}
obj* l_Lean_Elab_convertArrow___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_convertArrow(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertArrow");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertArrow___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertArrow(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Elab_convertHole___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean_expr_mk_mvar(x_1);
return x_2;
}
}
obj* l_Lean_Elab_convertHole___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_Elab_convertHole___rarg___closed__1;
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_Elab_convertHole___rarg___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_convertHole(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertHole___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_convertHole___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_convertHole(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertHole");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertHole___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertHole(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Elab_convertSorry___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("sorryAx");
return x_1;
}
}
obj* _init_l_Lean_Elab_convertSorry___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Elab_convertSorry___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Elab_convertSorry___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Elab_convertSorry___rarg___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Elab_convertSorry___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Elab_convertSorry___rarg___closed__3;
x_2 = l_Lean_Elab_convertHole___rarg___closed__1;
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Elab_convertSorry___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_Elab_convertSorry___rarg___closed__4;
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_Elab_convertSorry___rarg___closed__4;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_convertSorry(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertSorry___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_convertSorry___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_convertSorry(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("convertSorry");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_convertSorry___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSorry(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Term_sorry___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3;
x_5 = l_Lean_addBuiltinPreTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_oldElaborate(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
lean::inc(x_3);
lean::inc(x_1);
x_5 = l_Lean_Elab_toPreTerm(x_1, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = l_Lean_Elab_getScope___rarg(x_5);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::cnstr_set(x_9, 0, x_8);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
x_16 = lean::cnstr_get(x_12, 2);
x_17 = lean::cnstr_get(x_12, 3);
x_18 = lean::cnstr_get(x_12, 4);
x_19 = lean::cnstr_get(x_12, 5);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_11, 6);
lean::inc(x_21);
lean::dec(x_11);
x_22 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean::inc(x_20);
x_23 = lean_old_elaborate(x_14, x_20, x_18, x_21, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
lean::free_heap_obj(x_12);
lean::dec(x_19);
lean::dec(x_17);
lean::dec(x_16);
lean::dec(x_15);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_24, 1);
lean::inc(x_26);
lean::dec(x_24);
x_27 = l_Lean_Format_pretty(x_26, x_20);
lean::dec(x_20);
x_28 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_27, x_3, x_9);
lean::dec(x_3);
lean::dec(x_1);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
lean::dec(x_25);
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
x_32 = lean::box(0);
x_33 = l_Lean_Format_pretty(x_29, x_20);
lean::dec(x_20);
x_34 = 2;
x_35 = l_String_splitAux___main___closed__1;
x_36 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set(x_36, 1, x_30);
lean::cnstr_set(x_36, 2, x_32);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set(x_36, 4, x_33);
lean::cnstr_set_scalar(x_36, sizeof(void*)*5, x_34);
x_37 = l_Lean_Elab_logMessage(x_36, x_3, x_9);
lean::dec(x_3);
if (lean::obj_tag(x_37) == 0)
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_37, 0);
lean::dec(x_39);
x_40 = lean::box(4);
lean::cnstr_set_tag(x_37, 1);
lean::cnstr_set(x_37, 0, x_40);
return x_37;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
lean::dec(x_37);
x_42 = lean::box(4);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get(x_37, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_37);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_20);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_23, 0);
lean::inc(x_48);
lean::dec(x_23);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
lean::dec(x_48);
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
lean::cnstr_set(x_12, 4, x_51);
lean::cnstr_set(x_12, 0, x_50);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_12);
return x_53;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_54 = lean::cnstr_get(x_12, 0);
x_55 = lean::cnstr_get(x_12, 1);
x_56 = lean::cnstr_get(x_12, 2);
x_57 = lean::cnstr_get(x_12, 3);
x_58 = lean::cnstr_get(x_12, 4);
x_59 = lean::cnstr_get(x_12, 5);
lean::inc(x_59);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_12);
x_60 = lean::cnstr_get(x_11, 2);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_11, 6);
lean::inc(x_61);
lean::dec(x_11);
x_62 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean::inc(x_60);
x_63 = lean_old_elaborate(x_54, x_60, x_58, x_61, x_62);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_59);
lean::dec(x_57);
lean::dec(x_56);
lean::dec(x_55);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
lean::dec(x_63);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_67; obj* x_68; 
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
lean::dec(x_64);
x_67 = l_Lean_Format_pretty(x_66, x_60);
lean::dec(x_60);
x_68 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_67, x_3, x_9);
lean::dec(x_3);
lean::dec(x_1);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_1);
x_69 = lean::cnstr_get(x_64, 1);
lean::inc(x_69);
lean::dec(x_64);
x_70 = lean::cnstr_get(x_65, 0);
lean::inc(x_70);
lean::dec(x_65);
x_71 = lean::cnstr_get(x_3, 0);
lean::inc(x_71);
x_72 = lean::box(0);
x_73 = l_Lean_Format_pretty(x_69, x_60);
lean::dec(x_60);
x_74 = 2;
x_75 = l_String_splitAux___main___closed__1;
x_76 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_76, 0, x_71);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_72);
lean::cnstr_set(x_76, 3, x_75);
lean::cnstr_set(x_76, 4, x_73);
lean::cnstr_set_scalar(x_76, sizeof(void*)*5, x_74);
x_77 = l_Lean_Elab_logMessage(x_76, x_3, x_9);
lean::dec(x_3);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_78 = lean::cnstr_get(x_77, 1);
lean::inc(x_78);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_79 = x_77;
} else {
 lean::dec_ref(x_77);
 x_79 = lean::box(0);
}
x_80 = lean::box(4);
if (lean::is_scalar(x_79)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_79;
 lean::cnstr_set_tag(x_81, 1);
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_77, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_77, 1);
lean::inc(x_83);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_84 = x_77;
} else {
 lean::dec_ref(x_77);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
lean::cnstr_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_60);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_1);
x_86 = lean::cnstr_get(x_63, 0);
lean::inc(x_86);
lean::dec(x_63);
x_87 = lean::cnstr_get(x_86, 1);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 0);
lean::inc(x_88);
lean::dec(x_86);
x_89 = lean::cnstr_get(x_87, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_91 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_55);
lean::cnstr_set(x_91, 2, x_56);
lean::cnstr_set(x_91, 3, x_57);
lean::cnstr_set(x_91, 4, x_89);
lean::cnstr_set(x_91, 5, x_59);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_93 = lean::cnstr_get(x_9, 0);
x_94 = lean::cnstr_get(x_9, 1);
lean::inc(x_94);
lean::inc(x_93);
lean::dec(x_9);
lean::inc(x_94);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_8);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_94, 2);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_94, 3);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_94, 4);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_94, 5);
lean::inc(x_101);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 lean::cnstr_release(x_94, 2);
 lean::cnstr_release(x_94, 3);
 lean::cnstr_release(x_94, 4);
 lean::cnstr_release(x_94, 5);
 x_102 = x_94;
} else {
 lean::dec_ref(x_94);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_93, 2);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_93, 6);
lean::inc(x_104);
lean::dec(x_93);
x_105 = l_Lean_mkPreTypeAscriptionIfSome(x_7, x_2);
lean::inc(x_103);
x_106 = lean_old_elaborate(x_96, x_103, x_100, x_104, x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_107; obj* x_108; 
lean::dec(x_102);
lean::dec(x_101);
lean::dec(x_99);
lean::dec(x_98);
lean::dec(x_97);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
lean::dec(x_106);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
if (lean::obj_tag(x_108) == 0)
{
obj* x_109; obj* x_110; obj* x_111; 
x_109 = lean::cnstr_get(x_107, 1);
lean::inc(x_109);
lean::dec(x_107);
x_110 = l_Lean_Format_pretty(x_109, x_103);
lean::dec(x_103);
x_111 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_110, x_3, x_95);
lean::dec(x_3);
lean::dec(x_1);
return x_111;
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_1);
x_112 = lean::cnstr_get(x_107, 1);
lean::inc(x_112);
lean::dec(x_107);
x_113 = lean::cnstr_get(x_108, 0);
lean::inc(x_113);
lean::dec(x_108);
x_114 = lean::cnstr_get(x_3, 0);
lean::inc(x_114);
x_115 = lean::box(0);
x_116 = l_Lean_Format_pretty(x_112, x_103);
lean::dec(x_103);
x_117 = 2;
x_118 = l_String_splitAux___main___closed__1;
x_119 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_119, 0, x_114);
lean::cnstr_set(x_119, 1, x_113);
lean::cnstr_set(x_119, 2, x_115);
lean::cnstr_set(x_119, 3, x_118);
lean::cnstr_set(x_119, 4, x_116);
lean::cnstr_set_scalar(x_119, sizeof(void*)*5, x_117);
x_120 = l_Lean_Elab_logMessage(x_119, x_3, x_95);
lean::dec(x_3);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_121 = lean::cnstr_get(x_120, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_122 = x_120;
} else {
 lean::dec_ref(x_120);
 x_122 = lean::box(0);
}
x_123 = lean::box(4);
if (lean::is_scalar(x_122)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_122;
 lean::cnstr_set_tag(x_124, 1);
}
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_121);
return x_124;
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_125 = lean::cnstr_get(x_120, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_120, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_127 = x_120;
} else {
 lean::dec_ref(x_120);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_125);
lean::cnstr_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_103);
lean::dec(x_95);
lean::dec(x_3);
lean::dec(x_1);
x_129 = lean::cnstr_get(x_106, 0);
lean::inc(x_129);
lean::dec(x_106);
x_130 = lean::cnstr_get(x_129, 1);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_129, 0);
lean::inc(x_131);
lean::dec(x_129);
x_132 = lean::cnstr_get(x_130, 0);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
if (lean::is_scalar(x_102)) {
 x_134 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_134 = x_102;
}
lean::cnstr_set(x_134, 0, x_131);
lean::cnstr_set(x_134, 1, x_97);
lean::cnstr_set(x_134, 2, x_98);
lean::cnstr_set(x_134, 3, x_99);
lean::cnstr_set(x_134, 4, x_132);
lean::cnstr_set(x_134, 5, x_101);
x_135 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8 x_136; 
lean::dec(x_7);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_136 = !lean::is_exclusive(x_9);
if (x_136 == 0)
{
return x_9;
}
else
{
obj* x_137; obj* x_138; obj* x_139; 
x_137 = lean::cnstr_get(x_9, 0);
x_138 = lean::cnstr_get(x_9, 1);
lean::inc(x_138);
lean::inc(x_137);
lean::dec(x_9);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_137);
lean::cnstr_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_140 = lean::cnstr_get(x_5, 0);
x_141 = lean::cnstr_get(x_5, 1);
lean::inc(x_141);
lean::inc(x_140);
lean::dec(x_5);
x_142 = lean::box(0);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_141);
x_144 = l_Lean_Elab_getScope___rarg(x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_144, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_147 = x_144;
} else {
 lean::dec_ref(x_144);
 x_147 = lean::box(0);
}
lean::inc(x_146);
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_142);
lean::cnstr_set(x_148, 1, x_146);
x_149 = lean::cnstr_get(x_146, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_146, 1);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_146, 2);
lean::inc(x_151);
x_152 = lean::cnstr_get(x_146, 3);
lean::inc(x_152);
x_153 = lean::cnstr_get(x_146, 4);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_146, 5);
lean::inc(x_154);
if (lean::is_exclusive(x_146)) {
 lean::cnstr_release(x_146, 0);
 lean::cnstr_release(x_146, 1);
 lean::cnstr_release(x_146, 2);
 lean::cnstr_release(x_146, 3);
 lean::cnstr_release(x_146, 4);
 lean::cnstr_release(x_146, 5);
 x_155 = x_146;
} else {
 lean::dec_ref(x_146);
 x_155 = lean::box(0);
}
x_156 = lean::cnstr_get(x_145, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_145, 6);
lean::inc(x_157);
lean::dec(x_145);
x_158 = l_Lean_mkPreTypeAscriptionIfSome(x_140, x_2);
lean::inc(x_156);
x_159 = lean_old_elaborate(x_149, x_156, x_153, x_157, x_158);
if (lean::obj_tag(x_159) == 0)
{
obj* x_160; obj* x_161; 
lean::dec(x_155);
lean::dec(x_154);
lean::dec(x_152);
lean::dec(x_151);
lean::dec(x_150);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
lean::dec(x_159);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; 
x_162 = lean::cnstr_get(x_160, 1);
lean::inc(x_162);
lean::dec(x_160);
x_163 = l_Lean_Format_pretty(x_162, x_156);
lean::dec(x_156);
x_164 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_163, x_3, x_148);
lean::dec(x_3);
lean::dec(x_1);
return x_164;
}
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; uint8 x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_1);
x_165 = lean::cnstr_get(x_160, 1);
lean::inc(x_165);
lean::dec(x_160);
x_166 = lean::cnstr_get(x_161, 0);
lean::inc(x_166);
lean::dec(x_161);
x_167 = lean::cnstr_get(x_3, 0);
lean::inc(x_167);
x_168 = lean::box(0);
x_169 = l_Lean_Format_pretty(x_165, x_156);
lean::dec(x_156);
x_170 = 2;
x_171 = l_String_splitAux___main___closed__1;
x_172 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_172, 0, x_167);
lean::cnstr_set(x_172, 1, x_166);
lean::cnstr_set(x_172, 2, x_168);
lean::cnstr_set(x_172, 3, x_171);
lean::cnstr_set(x_172, 4, x_169);
lean::cnstr_set_scalar(x_172, sizeof(void*)*5, x_170);
x_173 = l_Lean_Elab_logMessage(x_172, x_3, x_148);
lean::dec(x_3);
if (lean::obj_tag(x_173) == 0)
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_174 = lean::cnstr_get(x_173, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 lean::cnstr_release(x_173, 1);
 x_175 = x_173;
} else {
 lean::dec_ref(x_173);
 x_175 = lean::box(0);
}
x_176 = lean::box(4);
if (lean::is_scalar(x_175)) {
 x_177 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_177 = x_175;
 lean::cnstr_set_tag(x_177, 1);
}
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_174);
return x_177;
}
else
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_178 = lean::cnstr_get(x_173, 0);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_173, 1);
lean::inc(x_179);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 lean::cnstr_release(x_173, 1);
 x_180 = x_173;
} else {
 lean::dec_ref(x_173);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_178);
lean::cnstr_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
lean::dec(x_156);
lean::dec(x_148);
lean::dec(x_3);
lean::dec(x_1);
x_182 = lean::cnstr_get(x_159, 0);
lean::inc(x_182);
lean::dec(x_159);
x_183 = lean::cnstr_get(x_182, 1);
lean::inc(x_183);
x_184 = lean::cnstr_get(x_182, 0);
lean::inc(x_184);
lean::dec(x_182);
x_185 = lean::cnstr_get(x_183, 0);
lean::inc(x_185);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::is_scalar(x_155)) {
 x_187 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_187 = x_155;
}
lean::cnstr_set(x_187, 0, x_184);
lean::cnstr_set(x_187, 1, x_150);
lean::cnstr_set(x_187, 2, x_151);
lean::cnstr_set(x_187, 3, x_152);
lean::cnstr_set(x_187, 4, x_185);
lean::cnstr_set(x_187, 5, x_154);
x_188 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_188, 0, x_186);
lean::cnstr_set(x_188, 1, x_187);
return x_188;
}
}
else
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; 
lean::dec(x_140);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_189 = lean::cnstr_get(x_144, 0);
lean::inc(x_189);
x_190 = lean::cnstr_get(x_144, 1);
lean::inc(x_190);
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_191 = x_144;
} else {
 lean::dec_ref(x_144);
 x_191 = lean::box(0);
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_189);
lean::cnstr_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
uint8 x_193; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_193 = !lean::is_exclusive(x_5);
if (x_193 == 0)
{
return x_5;
}
else
{
obj* x_194; obj* x_195; obj* x_196; 
x_194 = lean::cnstr_get(x_5, 0);
x_195 = lean::cnstr_get(x_5, 1);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_5);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
return x_196;
}
}
}
}
obj* initialize_init_lean_elaborator_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_preterm(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (io_result_is_error(w)) return w;
l_Lean_mkBuiltinPreTermElabTable___closed__1 = _init_l_Lean_mkBuiltinPreTermElabTable___closed__1();
lean::mark_persistent(l_Lean_mkBuiltinPreTermElabTable___closed__1);
w = l_Lean_mkBuiltinPreTermElabTable(w);
if (io_result_is_error(w)) return w;
l_Lean_builtinPreTermElabTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_builtinPreTermElabTable);
l_Lean_declareBuiltinPreTermElab___closed__1 = _init_l_Lean_declareBuiltinPreTermElab___closed__1();
lean::mark_persistent(l_Lean_declareBuiltinPreTermElab___closed__1);
l_Lean_declareBuiltinPreTermElab___closed__2 = _init_l_Lean_declareBuiltinPreTermElab___closed__2();
lean::mark_persistent(l_Lean_declareBuiltinPreTermElab___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__3);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4);
l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5 = _init_l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5);
l_Lean_registerBuiltinPreTermElabAttr___closed__1 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__1);
l_Lean_registerBuiltinPreTermElabAttr___closed__2 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__2);
l_Lean_registerBuiltinPreTermElabAttr___closed__3 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__3);
l_Lean_registerBuiltinPreTermElabAttr___closed__4 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__4);
l_Lean_registerBuiltinPreTermElabAttr___closed__5 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__5);
l_Lean_registerBuiltinPreTermElabAttr___closed__6 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__6();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__6);
l_Lean_registerBuiltinPreTermElabAttr___closed__7 = _init_l_Lean_registerBuiltinPreTermElabAttr___closed__7();
lean::mark_persistent(l_Lean_registerBuiltinPreTermElabAttr___closed__7);
w = l_Lean_registerBuiltinPreTermElabAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Expr_mkAnnotation___closed__1 = _init_l_Lean_Expr_mkAnnotation___closed__1();
lean::mark_persistent(l_Lean_Expr_mkAnnotation___closed__1);
l_Lean_Expr_mkAnnotation___closed__2 = _init_l_Lean_Expr_mkAnnotation___closed__2();
lean::mark_persistent(l_Lean_Expr_mkAnnotation___closed__2);
l___private_init_lean_elaborator_preterm_1__dummy___closed__1 = _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__1();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy___closed__1);
l___private_init_lean_elaborator_preterm_1__dummy___closed__2 = _init_l___private_init_lean_elaborator_preterm_1__dummy___closed__2();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy___closed__2);
l___private_init_lean_elaborator_preterm_1__dummy = _init_l___private_init_lean_elaborator_preterm_1__dummy();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_1__dummy);
l_Lean_mkAsIs___closed__1 = _init_l_Lean_mkAsIs___closed__1();
lean::mark_persistent(l_Lean_mkAsIs___closed__1);
l_Lean_mkAsIs___closed__2 = _init_l_Lean_mkAsIs___closed__2();
lean::mark_persistent(l_Lean_mkAsIs___closed__2);
l_Lean_mkPreTypeAscription___closed__1 = _init_l_Lean_mkPreTypeAscription___closed__1();
lean::mark_persistent(l_Lean_mkPreTypeAscription___closed__1);
l_Lean_mkPreTypeAscription___closed__2 = _init_l_Lean_mkPreTypeAscription___closed__2();
lean::mark_persistent(l_Lean_mkPreTypeAscription___closed__2);
l_Lean_mkPreTypeAscription___closed__3 = _init_l_Lean_mkPreTypeAscription___closed__3();
lean::mark_persistent(l_Lean_mkPreTypeAscription___closed__3);
l_Lean_Elab_toLevel___main___closed__1 = _init_l_Lean_Elab_toLevel___main___closed__1();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__1);
l_Lean_Elab_toLevel___main___closed__2 = _init_l_Lean_Elab_toLevel___main___closed__2();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__2);
l_Lean_Elab_toLevel___main___closed__3 = _init_l_Lean_Elab_toLevel___main___closed__3();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__3);
l_Lean_Elab_toLevel___main___closed__4 = _init_l_Lean_Elab_toLevel___main___closed__4();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__4);
l___private_init_lean_elaborator_preterm_2__setPos___closed__1 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__1();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__1);
l___private_init_lean_elaborator_preterm_2__setPos___closed__2 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__2();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__2);
l___private_init_lean_elaborator_preterm_2__setPos___closed__3 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__3();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__3);
l___private_init_lean_elaborator_preterm_2__setPos___closed__4 = _init_l___private_init_lean_elaborator_preterm_2__setPos___closed__4();
lean::mark_persistent(l___private_init_lean_elaborator_preterm_2__setPos___closed__4);
l_Lean_Elab_toPreTerm___closed__1 = _init_l_Lean_Elab_toPreTerm___closed__1();
lean::mark_persistent(l_Lean_Elab_toPreTerm___closed__1);
l_Lean_Elab_toPreTerm___closed__2 = _init_l_Lean_Elab_toPreTerm___closed__2();
lean::mark_persistent(l_Lean_Elab_toPreTerm___closed__2);
l_Lean_Elab_toPreTerm___closed__3 = _init_l_Lean_Elab_toPreTerm___closed__3();
lean::mark_persistent(l_Lean_Elab_toPreTerm___closed__3);
l_Lean_Elab_toPreTerm___closed__4 = _init_l_Lean_Elab_toPreTerm___closed__4();
lean::mark_persistent(l_Lean_Elab_toPreTerm___closed__4);
l_Lean_Elab_convertType___rarg___closed__1 = _init_l_Lean_Elab_convertType___rarg___closed__1();
lean::mark_persistent(l_Lean_Elab_convertType___rarg___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__3);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__4 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__4();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertType___closed__5 = _init_l___regBuiltinTermElab_Lean_Elab_convertType___closed__5();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertType___closed__5);
w = l___regBuiltinTermElab_Lean_Elab_convertType(w);
if (io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSort(w);
if (io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertProp___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertProp(w);
if (io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSortApp(w);
if (io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertArrow___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertArrow(w);
if (io_result_is_error(w)) return w;
l_Lean_Elab_convertHole___rarg___closed__1 = _init_l_Lean_Elab_convertHole___rarg___closed__1();
lean::mark_persistent(l_Lean_Elab_convertHole___rarg___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertHole___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertHole(w);
if (io_result_is_error(w)) return w;
l_Lean_Elab_convertSorry___rarg___closed__1 = _init_l_Lean_Elab_convertSorry___rarg___closed__1();
lean::mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__1);
l_Lean_Elab_convertSorry___rarg___closed__2 = _init_l_Lean_Elab_convertSorry___rarg___closed__2();
lean::mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__2);
l_Lean_Elab_convertSorry___rarg___closed__3 = _init_l_Lean_Elab_convertSorry___rarg___closed__3();
lean::mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__3);
l_Lean_Elab_convertSorry___rarg___closed__4 = _init_l_Lean_Elab_convertSorry___rarg___closed__4();
lean::mark_persistent(l_Lean_Elab_convertSorry___rarg___closed__4);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSorry___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSorry(w);
if (io_result_is_error(w)) return w;
return w;
}
