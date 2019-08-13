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
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
extern obj* l_Lean_Parser_indexed___rarg___closed__1;
obj* l_Lean_addBuiltinPreTermElab(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__2;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__3;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__5;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_Lean_Syntax_getKind___rarg(obj*);
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(obj*, obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_builtinPreTermElabTable;
obj* l_Lean_Elab_convertType___rarg(obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__4;
extern obj* l_Lean_AttributeImpl_inhabited___closed__5;
extern obj* l_Lean_Parser_Level_max___elambda__1___closed__1;
obj* l_HashMapImp_insert___at_Lean_addBuiltinPreTermElab___spec__3(obj*, obj*, obj*);
extern obj* l_Lean_addBuiltinTermElab___closed__2;
obj* l_Lean_mkBuiltinPreTermElabTable___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__3;
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2;
extern "C" obj* level_mk_mvar(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__7;
obj* l_Lean_Elab_convertSort___boxed(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__5;
obj* l_Lean_Elab_convertType(obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_mkInitAttr___lambda__1___closed__1;
extern obj* l_Lean_Parser_Level_hole___elambda__1___rarg___closed__2;
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__4;
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3;
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
extern obj* l_Lean_AttributeImpl_inhabited___closed__4;
obj* l_Lean_registerTagAttribute___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_preterm_1__dummy;
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__1;
obj* l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1___boxed(obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr(obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Elab_convertSort(obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_Elab_toPreTerm___closed__1;
extern obj* l_Lean_numLitKind___closed__2;
obj* l_Lean_Syntax_getArg___rarg(obj*, obj*);
obj* l_Lean_Elab_toLevel___main___closed__2;
extern obj* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__3;
obj* l_Lean_Elab_convertSortApp(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
uint8 l_Lean_Syntax_isOfKind___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
extern obj* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__1;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1___boxed(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
extern obj* l_Lean_addBuiltinTermElab___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__4;
obj* l___private_init_lean_elaborator_preterm_1__dummy___closed__2;
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1(obj*, obj*, obj*, uint8, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_HashMapImp_contains___at_Lean_addBuiltinPreTermElab___spec__1(obj*, obj*);
extern obj* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
extern obj* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
obj* l_Lean_Elab_convertSort___rarg(obj*);
obj* l_Lean_addBuiltinPreTermElab___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_Elab_toPreTerm___spec__2___boxed(obj*, obj*);
obj* l_Lean_syntaxNodeKindOfAttrParam(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___closed__6;
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(obj*, obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__4;
obj* l_HashMapImp_expand___at_Lean_addBuiltinPreTermElab___spec__4(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertType(obj*);
extern obj* l_Lean_Level_one___closed__1;
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinPreTermElab___spec__5(obj*, obj*, obj*);
obj* l_Lean_Elab_toPreTerm___closed__3;
extern "C" obj* level_mk_succ(obj*);
extern obj* l_System_FilePath_dirName___closed__1;
obj* l_Lean_Elab_toLevel___main___closed__1;
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_Expr_mkAnnotation___closed__1;
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Lean_ConstantInfo_type(obj*);
obj* l_Lean_Expr_mkAnnotation(obj*, obj*);
obj* l_Lean_mkBuiltinPreTermElabTable(obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSort___closed__1;
obj* l_Lean_Elab_toPreTerm(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinPreTermElab___spec__6(obj*, obj*);
obj* l_Lean_Level_addOffsetAux___main(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Elab_toLevel(obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_convertType___boxed(obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_convertSortApp(obj*);
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__2;
extern obj* l_Lean_nameToExprAux___main___closed__4;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___regBuiltinTermElab_Lean_Elab_convertSort(obj*);
obj* l_Lean_Syntax_toNat___rarg(obj*);
extern obj* l_Lean_Parser_Level_imax___elambda__1___closed__1;
obj* l_AssocList_replace___main___at_Lean_addBuiltinPreTermElab___spec__7(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinElab(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_convertSortApp___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_toLevel___main___closed__3;
obj* l_Lean_Elab_toLevel___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_AssocList_contains___main___at_Lean_addBuiltinPreTermElab___spec__2___boxed(obj*, obj*);
obj* l_Lean_Expr_mkAnnotation___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_Elab_convertType___rarg___closed__1;
extern obj* l_Lean_exprIsInhabited___closed__1;
obj* l_Lean_registerBuiltinPreTermElabAttr___lambda__1___closed__5;
obj* l_Lean_declareBuiltinPreTermElab(obj*, obj*, obj*, obj*);
obj* l_Lean_logErrorAndThrow___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_toPreTerm___closed__4;
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
x_30 = lean::environment_find_core(x_1, x_2);
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
x_61 = lean::environment_find_core(x_1, x_2);
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
x_13 = l_Lean_numLitKind___closed__2;
x_14 = lean_name_dec_eq(x_4, x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = l_Lean_Parser_indexed___rarg___closed__1;
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
obj* x_45; obj* x_46; 
lean::dec(x_4);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
lean::closure_set(x_45, 0, x_1);
x_46 = l_Lean_Elab_runIOUnsafe___rarg(x_45, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_46, 0);
lean::dec(x_48);
x_49 = lean::box(0);
lean::cnstr_set(x_46, 0, x_49);
return x_46;
}
else
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::cnstr_get(x_46, 1);
lean::inc(x_50);
lean::dec(x_46);
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8 x_53; 
x_53 = !lean::is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_46, 0);
x_55 = lean::cnstr_get(x_46, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_46);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8 x_57; 
lean::dec(x_4);
x_57 = !lean::is_exclusive(x_3);
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::cnstr_get(x_3, 0);
lean::dec(x_58);
x_59 = l_Lean_Syntax_toNat___rarg(x_1);
lean::dec(x_1);
x_60 = l_Lean_Level_ofNat___main(x_59);
lean::dec(x_59);
lean::cnstr_set(x_3, 0, x_60);
return x_3;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_3, 1);
lean::inc(x_61);
lean::dec(x_3);
x_62 = l_Lean_Syntax_toNat___rarg(x_1);
lean::dec(x_1);
x_63 = l_Lean_Level_ofNat___main(x_62);
lean::dec(x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_61);
return x_64;
}
}
}
else
{
uint8 x_65; 
lean::dec(x_4);
lean::dec(x_1);
x_65 = !lean::is_exclusive(x_3);
if (x_65 == 0)
{
obj* x_66; obj* x_67; 
x_66 = lean::cnstr_get(x_3, 0);
lean::dec(x_66);
x_67 = l_Lean_Elab_toLevel___main___closed__3;
lean::cnstr_set(x_3, 0, x_67);
return x_3;
}
else
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_3, 1);
lean::inc(x_68);
lean::dec(x_3);
x_69 = l_Lean_Elab_toLevel___main___closed__3;
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_4);
lean::dec(x_1);
x_71 = !lean::is_exclusive(x_3);
if (x_71 == 0)
{
obj* x_72; obj* x_73; 
x_72 = lean::cnstr_get(x_3, 0);
lean::dec(x_72);
x_73 = lean::box(0);
lean::cnstr_set(x_3, 0, x_73);
return x_3;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_3, 1);
lean::inc(x_74);
lean::dec(x_3);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
obj* x_77; obj* x_78; 
lean::dec(x_4);
x_77 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
lean::closure_set(x_77, 0, x_1);
x_78 = l_Lean_Elab_runIOUnsafe___rarg(x_77, x_2, x_3);
if (lean::obj_tag(x_78) == 0)
{
uint8 x_79; 
x_79 = !lean::is_exclusive(x_78);
if (x_79 == 0)
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_78, 0);
lean::dec(x_80);
x_81 = lean::box(0);
lean::cnstr_set(x_78, 0, x_81);
return x_78;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_78, 1);
lean::inc(x_82);
lean::dec(x_78);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_78);
if (x_85 == 0)
{
return x_78;
}
else
{
obj* x_86; obj* x_87; obj* x_88; 
x_86 = lean::cnstr_get(x_78, 0);
x_87 = lean::cnstr_get(x_78, 1);
lean::inc(x_87);
lean::inc(x_86);
lean::dec(x_78);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
obj* x_89; obj* x_90; 
lean::dec(x_4);
x_89 = lean::mk_nat_obj(1u);
x_90 = l_Lean_Syntax_getArg___rarg(x_1, x_89);
lean::dec(x_1);
x_1 = x_90;
goto _start;
}
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
x_19 = l_Lean_logErrorAndThrow___rarg(x_1, x_18, x_2, x_9);
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
x_21 = lean::apply_3(x_20, x_1, x_2, x_9);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_9, 0);
x_23 = lean::cnstr_get(x_9, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_9);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_7);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_22, x_4);
lean::dec(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_4);
x_28 = l_Lean_Elab_toPreTerm___closed__4;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean::string_append(x_29, x_30);
x_32 = l_Lean_logErrorAndThrow___rarg(x_1, x_31, x_2, x_24);
lean::dec(x_2);
lean::dec(x_1);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_4);
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_34 = lean::apply_3(x_33, x_1, x_2, x_24);
return x_34;
}
}
}
else
{
uint8 x_35; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_35 = !lean::is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_9, 0);
x_37 = lean::cnstr_get(x_9, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_9);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_3, 1);
lean::inc(x_39);
lean::dec(x_3);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_toPreTerm___closed__3;
x_43 = l_Lean_Elab_runIOUnsafe___rarg(x_42, x_2, x_41);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_43, 1);
lean::inc(x_45);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_46 = x_43;
} else {
 lean::dec_ref(x_43);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_40);
lean::cnstr_set(x_47, 1, x_45);
x_48 = l_HashMapImp_find___at_Lean_Elab_toPreTerm___spec__1(x_44, x_4);
lean::dec(x_44);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_49 = l_System_FilePath_dirName___closed__1;
x_50 = l_Lean_Name_toStringWithSep___main(x_49, x_4);
x_51 = l_Lean_Elab_toPreTerm___closed__4;
x_52 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_53 = l_Char_HasRepr___closed__1;
x_54 = lean::string_append(x_52, x_53);
x_55 = l_Lean_logErrorAndThrow___rarg(x_1, x_54, x_2, x_47);
lean::dec(x_2);
lean::dec(x_1);
return x_55;
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_4);
x_56 = lean::cnstr_get(x_48, 0);
lean::inc(x_56);
lean::dec(x_48);
x_57 = lean::apply_3(x_56, x_1, x_2, x_47);
return x_57;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_58 = lean::cnstr_get(x_43, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_43, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_60 = x_43;
} else {
 lean::dec_ref(x_43);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8 x_62; 
lean::dec(x_2);
lean::dec(x_1);
x_62 = !lean::is_exclusive(x_3);
if (x_62 == 0)
{
obj* x_63; obj* x_64; 
x_63 = lean::cnstr_get(x_3, 0);
lean::dec(x_63);
x_64 = l_Lean_Elab_toPreTerm___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_64);
return x_3;
}
else
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_3, 1);
lean::inc(x_65);
lean::dec(x_3);
x_66 = l_Lean_Elab_toPreTerm___closed__2;
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_65);
return x_67;
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
l_Lean_Elab_toLevel___main___closed__1 = _init_l_Lean_Elab_toLevel___main___closed__1();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__1);
l_Lean_Elab_toLevel___main___closed__2 = _init_l_Lean_Elab_toLevel___main___closed__2();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__2);
l_Lean_Elab_toLevel___main___closed__3 = _init_l_Lean_Elab_toLevel___main___closed__3();
lean::mark_persistent(l_Lean_Elab_toLevel___main___closed__3);
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
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_convertSortApp___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_convertSortApp(w);
if (io_result_is_error(w)) return w;
return w;
}
