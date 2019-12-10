// Lean compiler output
// Module: Init.Lean.Elab.Quotation
// Imports: Init.Lean.Syntax Init.Lean.Elab.ResolveName Init.Lean.Parser
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
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserContextCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main(lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11;
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2;
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5;
extern lean_object* l_Lean_stxInh;
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Literal_type___closed__5;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_3__appN___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_stxQuot_expand(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1;
lean_object* l_Lean_Parser_ParserAttribute_runParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19;
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_cons___elambda__1___closed__1;
extern lean_object* l_Lean_FileMap_ofString___closed__1;
extern lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
extern lean_object* l_Lean_Parser_termParserAttribute;
extern lean_object* l_Lean_nameToExprAux___main___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2;
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
extern lean_object* l_Lean_numLitKind;
extern lean_object* l_Lean_strLitKind;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__1;
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName(lean_object*);
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_1__const(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
lean_object* l_Lean_Syntax_isStrLit(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_formatStx___main___closed__5;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__9;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6;
lean_object* l_Lean_Elab_oldParseStxQuot___closed__1;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_3__appN(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3;
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_stxQuot_expand___closed__3;
lean_object* l_Lean_Elab_stxQuot_expand___closed__5;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10;
extern lean_object* l_Lean_Parser_symbolOrIdentInfo___closed__1;
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_stxQuot_expand___closed__4;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_parse_stx_quot(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5;
lean_object* l___private_Init_Lean_Elab_Quotation_2__app(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4;
extern lean_object* l_Lean_nameToExprAux___main___closed__6;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_stxQuot_expand___closed__2;
extern lean_object* l_String_Inhabited;
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7;
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(lean_object*, lean_object*);
lean_object* l_Lean_Elab_stxQuot_expand___closed__1;
lean_object* l_Lean_Elab_stxQuot_expand___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Quotation_1__const(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_box(0);
x_3 = l_System_FilePath_dirName___closed__1;
lean_inc(x_1);
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_1);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_11, 3, x_10);
x_12 = l_Lean_FileMap_ofString___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_2__app(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l___private_Init_Lean_Elab_Quotation_2__app(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_3__appN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_3__appN___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Quotation_3__appN(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameToExprAux___main___closed__6;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameToExprAux___main___closed__9;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_nameToExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_nameToExprAux___main___closed__2;
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_nameToExprAux___main___closed__3;
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = l___private_Init_Lean_Elab_Quotation_1__const(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_strLitKind;
x_14 = l_Lean_mkStxLit(x_13, x_10, x_12);
x_15 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_14);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1;
x_20 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_17, x_17, x_18, x_19);
lean_dec(x_17);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_21);
x_24 = l_Nat_repr(x_22);
x_25 = lean_box(0);
x_26 = l_Lean_numLitKind;
x_27 = l_Lean_mkStxLit(x_26, x_24, x_25);
x_28 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_29 = lean_array_push(x_28, x_23);
x_30 = lean_array_push(x_29, x_27);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2;
x_33 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_30, x_30, x_31, x_32);
lean_dec(x_30);
return x_33;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_4__quoteName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2;
x_2 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2;
x_2 = l_Lean_Parser_Term_cons___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_4);
x_6 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_7, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7;
x_11 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_8, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArray");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2;
x_2 = l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_2);
x_4 = l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3;
x_5 = l___private_Init_Lean_Elab_Quotation_2__app(x_4, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_6__quoteArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
x_12 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_strLitKind;
lean_inc(x_1);
x_8 = l_Lean_mkStxLit(x_7, x_5, x_1);
x_9 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_strLitKind;
lean_inc(x_1);
x_13 = l_Lean_mkStxLit(x_12, x_10, x_1);
x_14 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
lean_object* _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
lean_object* _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2;
x_2 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11(x_1, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_8);
x_11 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(x_1, x_9);
x_12 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_11);
x_13 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5;
x_18 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_15, x_15, x_16, x_17);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_21 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11(x_1, x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_22);
x_25 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__10(x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_25);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_28 = lean_array_push(x_27, x_24);
x_29 = lean_array_push(x_28, x_26);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5;
x_32 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_29, x_29, x_30, x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Syntax");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("node");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("atom");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10;
x_2 = l_Option_HasRepr___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2;
x_2 = l_Lean_Parser_symbolOrIdentInfo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toSubstring");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__5;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_2 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_stxInh;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2(x_1, x_18, x_6);
x_20 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_19);
lean_dec(x_19);
x_21 = l_Lean_nameToExprAux___main___closed__1;
x_22 = lean_name_mk_string(x_5, x_21);
x_23 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_24 = lean_name_mk_string(x_22, x_23);
x_25 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_26 = lean_name_mk_string(x_24, x_25);
x_27 = l___private_Init_Lean_Elab_Quotation_1__const(x_26);
x_28 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_29 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_30 = lean_array_push(x_29, x_28);
x_31 = lean_array_push(x_30, x_20);
x_32 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_31, x_31, x_18, x_27);
lean_dec(x_31);
return x_32;
}
case 1:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3(x_1, x_34, x_6);
x_36 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_35);
lean_dec(x_35);
x_37 = l_Lean_nameToExprAux___main___closed__1;
x_38 = lean_name_mk_string(x_33, x_37);
x_39 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_40 = lean_name_mk_string(x_38, x_39);
x_41 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_42 = lean_name_mk_string(x_40, x_41);
x_43 = l___private_Init_Lean_Elab_Quotation_1__const(x_42);
x_44 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_45 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_46 = lean_array_push(x_45, x_44);
x_47 = lean_array_push(x_46, x_36);
x_48 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_47, x_47, x_34, x_43);
lean_dec(x_47);
return x_48;
}
case 1:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
switch (lean_obj_tag(x_49)) {
case 0:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_33);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4(x_1, x_50, x_6);
x_52 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_51);
lean_dec(x_51);
x_53 = l_Lean_nameToExprAux___main___closed__1;
x_54 = lean_name_mk_string(x_49, x_53);
x_55 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_56 = lean_name_mk_string(x_54, x_55);
x_57 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_58 = lean_name_mk_string(x_56, x_57);
x_59 = l___private_Init_Lean_Elab_Quotation_1__const(x_58);
x_60 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_61 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_62 = lean_array_push(x_61, x_60);
x_63 = lean_array_push(x_62, x_52);
x_64 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_63, x_63, x_50, x_59);
lean_dec(x_63);
return x_64;
}
case 1:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
switch (lean_obj_tag(x_65)) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_49);
lean_dec(x_33);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5(x_1, x_66, x_6);
x_68 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_67);
lean_dec(x_67);
x_69 = l_Lean_nameToExprAux___main___closed__1;
x_70 = lean_name_mk_string(x_65, x_69);
x_71 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_72 = lean_name_mk_string(x_70, x_71);
x_73 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_74 = lean_name_mk_string(x_72, x_73);
x_75 = l___private_Init_Lean_Elab_Quotation_1__const(x_74);
x_76 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_77 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_78 = lean_array_push(x_77, x_76);
x_79 = lean_array_push(x_78, x_68);
x_80 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_79, x_79, x_66, x_75);
lean_dec(x_79);
return x_80;
}
case 1:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_5, 1);
lean_inc(x_82);
x_83 = !lean_is_exclusive(x_33);
if (x_83 == 0)
{
size_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get_usize(x_5, 2);
x_85 = lean_ctor_get(x_33, 1);
x_86 = lean_ctor_get(x_33, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_49);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_49, 1);
x_89 = lean_ctor_get(x_49, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_65, 1);
x_92 = lean_ctor_get(x_65, 0);
lean_dec(x_92);
x_93 = l_Lean_nameToExprAux___main___closed__1;
x_94 = lean_string_dec_eq(x_91, x_93);
lean_dec(x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_free_object(x_65);
lean_free_object(x_49);
lean_dec(x_88);
lean_free_object(x_33);
lean_dec(x_85);
lean_dec(x_82);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(x_1, x_95, x_6);
x_97 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_96);
lean_dec(x_96);
x_98 = lean_name_mk_string(x_81, x_93);
x_99 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_100 = lean_name_mk_string(x_98, x_99);
x_101 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_102 = lean_name_mk_string(x_100, x_101);
x_103 = l___private_Init_Lean_Elab_Quotation_1__const(x_102);
x_104 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_105 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_106 = lean_array_push(x_105, x_104);
x_107 = lean_array_push(x_106, x_97);
x_108 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_107, x_107, x_95, x_103);
lean_dec(x_107);
return x_108;
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_5);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_5, 1);
lean_dec(x_110);
x_111 = lean_ctor_get(x_5, 0);
lean_dec(x_111);
x_112 = l_Lean_Syntax_formatStx___main___closed__5;
x_113 = lean_string_dec_eq(x_88, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_114, x_6);
x_116 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_115);
lean_dec(x_115);
x_117 = lean_name_mk_string(x_81, x_93);
x_118 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_119 = lean_name_mk_string(x_117, x_118);
x_120 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_121 = lean_name_mk_string(x_119, x_120);
x_122 = l___private_Init_Lean_Elab_Quotation_1__const(x_121);
lean_ctor_set(x_65, 1, x_93);
x_123 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_124 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_125 = lean_array_push(x_124, x_123);
x_126 = lean_array_push(x_125, x_116);
x_127 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_126, x_126, x_114, x_122);
lean_dec(x_126);
return x_127;
}
else
{
lean_object* x_128; uint8_t x_129; 
lean_dec(x_88);
x_128 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_129 = lean_string_dec_eq(x_85, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_130, x_6);
x_132 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_131);
lean_dec(x_131);
x_133 = lean_name_mk_string(x_81, x_93);
x_134 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_135 = lean_name_mk_string(x_133, x_134);
x_136 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_137 = lean_name_mk_string(x_135, x_136);
x_138 = l___private_Init_Lean_Elab_Quotation_1__const(x_137);
lean_ctor_set(x_65, 1, x_93);
lean_ctor_set(x_49, 1, x_112);
x_139 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_140 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_141 = lean_array_push(x_140, x_139);
x_142 = lean_array_push(x_141, x_132);
x_143 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_142, x_142, x_130, x_138);
lean_dec(x_142);
return x_143;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_85);
x_144 = l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
x_145 = lean_string_dec_eq(x_82, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_146, x_6);
x_148 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_147);
lean_dec(x_147);
x_149 = lean_name_mk_string(x_81, x_93);
x_150 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_151 = lean_name_mk_string(x_149, x_150);
x_152 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_153 = lean_name_mk_string(x_151, x_152);
x_154 = l___private_Init_Lean_Elab_Quotation_1__const(x_153);
lean_ctor_set(x_65, 1, x_93);
lean_ctor_set(x_49, 1, x_112);
lean_ctor_set(x_33, 1, x_128);
x_155 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_156 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_157 = lean_array_push(x_156, x_155);
x_158 = lean_array_push(x_157, x_148);
x_159 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_158, x_158, x_146, x_154);
lean_dec(x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_free_object(x_5);
lean_free_object(x_65);
lean_free_object(x_49);
lean_free_object(x_33);
lean_dec(x_82);
x_160 = l_Lean_stxInh;
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_array_get(x_160, x_6, x_161);
lean_dec(x_6);
return x_162;
}
}
}
}
else
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_5);
x_163 = l_Lean_Syntax_formatStx___main___closed__5;
x_164 = lean_string_dec_eq(x_88, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_165, x_6);
x_167 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_166);
lean_dec(x_166);
x_168 = lean_name_mk_string(x_81, x_93);
x_169 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_170 = lean_name_mk_string(x_168, x_169);
x_171 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_172 = lean_name_mk_string(x_170, x_171);
x_173 = l___private_Init_Lean_Elab_Quotation_1__const(x_172);
lean_ctor_set(x_65, 1, x_93);
x_174 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_174, 0, x_33);
lean_ctor_set(x_174, 1, x_82);
lean_ctor_set_usize(x_174, 2, x_84);
x_175 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_174);
x_176 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_177 = lean_array_push(x_176, x_175);
x_178 = lean_array_push(x_177, x_167);
x_179 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_178, x_178, x_165, x_173);
lean_dec(x_178);
return x_179;
}
else
{
lean_object* x_180; uint8_t x_181; 
lean_dec(x_88);
x_180 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_181 = lean_string_dec_eq(x_85, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_182, x_6);
x_184 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_183);
lean_dec(x_183);
x_185 = lean_name_mk_string(x_81, x_93);
x_186 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_187 = lean_name_mk_string(x_185, x_186);
x_188 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_189 = lean_name_mk_string(x_187, x_188);
x_190 = l___private_Init_Lean_Elab_Quotation_1__const(x_189);
lean_ctor_set(x_65, 1, x_93);
lean_ctor_set(x_49, 1, x_163);
x_191 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_191, 0, x_33);
lean_ctor_set(x_191, 1, x_82);
lean_ctor_set_usize(x_191, 2, x_84);
x_192 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_191);
x_193 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_194 = lean_array_push(x_193, x_192);
x_195 = lean_array_push(x_194, x_184);
x_196 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_195, x_195, x_182, x_190);
lean_dec(x_195);
return x_196;
}
else
{
lean_object* x_197; uint8_t x_198; 
lean_dec(x_85);
x_197 = l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
x_198 = lean_string_dec_eq(x_82, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_199, x_6);
x_201 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_200);
lean_dec(x_200);
x_202 = lean_name_mk_string(x_81, x_93);
x_203 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_204 = lean_name_mk_string(x_202, x_203);
x_205 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_206 = lean_name_mk_string(x_204, x_205);
x_207 = l___private_Init_Lean_Elab_Quotation_1__const(x_206);
lean_ctor_set(x_65, 1, x_93);
lean_ctor_set(x_49, 1, x_163);
lean_ctor_set(x_33, 1, x_180);
x_208 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_208, 0, x_33);
lean_ctor_set(x_208, 1, x_82);
lean_ctor_set_usize(x_208, 2, x_84);
x_209 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_208);
x_210 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_211 = lean_array_push(x_210, x_209);
x_212 = lean_array_push(x_211, x_201);
x_213 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_212, x_212, x_199, x_207);
lean_dec(x_212);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_free_object(x_65);
lean_free_object(x_49);
lean_free_object(x_33);
lean_dec(x_82);
x_214 = l_Lean_stxInh;
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_array_get(x_214, x_6, x_215);
lean_dec(x_6);
return x_216;
}
}
}
}
}
}
else
{
lean_object* x_217; size_t x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_65, 1);
x_218 = lean_ctor_get_usize(x_65, 2);
lean_inc(x_217);
lean_dec(x_65);
x_219 = l_Lean_nameToExprAux___main___closed__1;
x_220 = lean_string_dec_eq(x_217, x_219);
lean_dec(x_217);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_free_object(x_49);
lean_dec(x_88);
lean_free_object(x_33);
lean_dec(x_85);
lean_dec(x_82);
x_221 = lean_unsigned_to_nat(0u);
x_222 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(x_1, x_221, x_6);
x_223 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_222);
lean_dec(x_222);
x_224 = lean_name_mk_string(x_81, x_219);
x_225 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_226 = lean_name_mk_string(x_224, x_225);
x_227 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_228 = lean_name_mk_string(x_226, x_227);
x_229 = l___private_Init_Lean_Elab_Quotation_1__const(x_228);
x_230 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_231 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_232 = lean_array_push(x_231, x_230);
x_233 = lean_array_push(x_232, x_223);
x_234 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_233, x_233, x_221, x_229);
lean_dec(x_233);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_235 = x_5;
} else {
 lean_dec_ref(x_5);
 x_235 = lean_box(0);
}
x_236 = l_Lean_Syntax_formatStx___main___closed__5;
x_237 = lean_string_dec_eq(x_88, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_238 = lean_unsigned_to_nat(0u);
x_239 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_238, x_6);
x_240 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_239);
lean_dec(x_239);
x_241 = lean_name_mk_string(x_81, x_219);
x_242 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_243 = lean_name_mk_string(x_241, x_242);
x_244 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_245 = lean_name_mk_string(x_243, x_244);
x_246 = l___private_Init_Lean_Elab_Quotation_1__const(x_245);
x_247 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_247, 0, x_81);
lean_ctor_set(x_247, 1, x_219);
lean_ctor_set_usize(x_247, 2, x_218);
lean_ctor_set(x_49, 0, x_247);
if (lean_is_scalar(x_235)) {
 x_248 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_248 = x_235;
}
lean_ctor_set(x_248, 0, x_33);
lean_ctor_set(x_248, 1, x_82);
lean_ctor_set_usize(x_248, 2, x_84);
x_249 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_248);
x_250 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_251 = lean_array_push(x_250, x_249);
x_252 = lean_array_push(x_251, x_240);
x_253 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_252, x_252, x_238, x_246);
lean_dec(x_252);
return x_253;
}
else
{
lean_object* x_254; uint8_t x_255; 
lean_dec(x_88);
x_254 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_255 = lean_string_dec_eq(x_85, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_256, x_6);
x_258 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_257);
lean_dec(x_257);
x_259 = lean_name_mk_string(x_81, x_219);
x_260 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_261 = lean_name_mk_string(x_259, x_260);
x_262 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_263 = lean_name_mk_string(x_261, x_262);
x_264 = l___private_Init_Lean_Elab_Quotation_1__const(x_263);
x_265 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_265, 0, x_81);
lean_ctor_set(x_265, 1, x_219);
lean_ctor_set_usize(x_265, 2, x_218);
lean_ctor_set(x_49, 1, x_236);
lean_ctor_set(x_49, 0, x_265);
if (lean_is_scalar(x_235)) {
 x_266 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_266 = x_235;
}
lean_ctor_set(x_266, 0, x_33);
lean_ctor_set(x_266, 1, x_82);
lean_ctor_set_usize(x_266, 2, x_84);
x_267 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_266);
x_268 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_269 = lean_array_push(x_268, x_267);
x_270 = lean_array_push(x_269, x_258);
x_271 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_270, x_270, x_256, x_264);
lean_dec(x_270);
return x_271;
}
else
{
lean_object* x_272; uint8_t x_273; 
lean_dec(x_85);
x_272 = l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
x_273 = lean_string_dec_eq(x_82, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_274 = lean_unsigned_to_nat(0u);
x_275 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_274, x_6);
x_276 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_275);
lean_dec(x_275);
x_277 = lean_name_mk_string(x_81, x_219);
x_278 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_279 = lean_name_mk_string(x_277, x_278);
x_280 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_281 = lean_name_mk_string(x_279, x_280);
x_282 = l___private_Init_Lean_Elab_Quotation_1__const(x_281);
x_283 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_283, 0, x_81);
lean_ctor_set(x_283, 1, x_219);
lean_ctor_set_usize(x_283, 2, x_218);
lean_ctor_set(x_49, 1, x_236);
lean_ctor_set(x_49, 0, x_283);
lean_ctor_set(x_33, 1, x_254);
if (lean_is_scalar(x_235)) {
 x_284 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_284 = x_235;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_82);
lean_ctor_set_usize(x_284, 2, x_84);
x_285 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_284);
x_286 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_287 = lean_array_push(x_286, x_285);
x_288 = lean_array_push(x_287, x_276);
x_289 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_288, x_288, x_274, x_282);
lean_dec(x_288);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_235);
lean_free_object(x_49);
lean_free_object(x_33);
lean_dec(x_82);
x_290 = l_Lean_stxInh;
x_291 = lean_unsigned_to_nat(1u);
x_292 = lean_array_get(x_290, x_6, x_291);
lean_dec(x_6);
return x_292;
}
}
}
}
}
}
else
{
lean_object* x_293; size_t x_294; lean_object* x_295; size_t x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_293 = lean_ctor_get(x_49, 1);
x_294 = lean_ctor_get_usize(x_49, 2);
lean_inc(x_293);
lean_dec(x_49);
x_295 = lean_ctor_get(x_65, 1);
lean_inc(x_295);
x_296 = lean_ctor_get_usize(x_65, 2);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_297 = x_65;
} else {
 lean_dec_ref(x_65);
 x_297 = lean_box(0);
}
x_298 = l_Lean_nameToExprAux___main___closed__1;
x_299 = lean_string_dec_eq(x_295, x_298);
lean_dec(x_295);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_297);
lean_dec(x_293);
lean_free_object(x_33);
lean_dec(x_85);
lean_dec(x_82);
x_300 = lean_unsigned_to_nat(0u);
x_301 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(x_1, x_300, x_6);
x_302 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_301);
lean_dec(x_301);
x_303 = lean_name_mk_string(x_81, x_298);
x_304 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_305 = lean_name_mk_string(x_303, x_304);
x_306 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_307 = lean_name_mk_string(x_305, x_306);
x_308 = l___private_Init_Lean_Elab_Quotation_1__const(x_307);
x_309 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_310 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_311 = lean_array_push(x_310, x_309);
x_312 = lean_array_push(x_311, x_302);
x_313 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_312, x_312, x_300, x_308);
lean_dec(x_312);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_314 = x_5;
} else {
 lean_dec_ref(x_5);
 x_314 = lean_box(0);
}
x_315 = l_Lean_Syntax_formatStx___main___closed__5;
x_316 = lean_string_dec_eq(x_293, x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_317 = lean_unsigned_to_nat(0u);
x_318 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_317, x_6);
x_319 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_318);
lean_dec(x_318);
x_320 = lean_name_mk_string(x_81, x_298);
x_321 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_322 = lean_name_mk_string(x_320, x_321);
x_323 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_324 = lean_name_mk_string(x_322, x_323);
x_325 = l___private_Init_Lean_Elab_Quotation_1__const(x_324);
if (lean_is_scalar(x_297)) {
 x_326 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_326 = x_297;
}
lean_ctor_set(x_326, 0, x_81);
lean_ctor_set(x_326, 1, x_298);
lean_ctor_set_usize(x_326, 2, x_296);
x_327 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_293);
lean_ctor_set_usize(x_327, 2, x_294);
lean_ctor_set(x_33, 0, x_327);
if (lean_is_scalar(x_314)) {
 x_328 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_328 = x_314;
}
lean_ctor_set(x_328, 0, x_33);
lean_ctor_set(x_328, 1, x_82);
lean_ctor_set_usize(x_328, 2, x_84);
x_329 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_328);
x_330 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_331 = lean_array_push(x_330, x_329);
x_332 = lean_array_push(x_331, x_319);
x_333 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_332, x_332, x_317, x_325);
lean_dec(x_332);
return x_333;
}
else
{
lean_object* x_334; uint8_t x_335; 
lean_dec(x_293);
x_334 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_335 = lean_string_dec_eq(x_85, x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_336, x_6);
x_338 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_337);
lean_dec(x_337);
x_339 = lean_name_mk_string(x_81, x_298);
x_340 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_341 = lean_name_mk_string(x_339, x_340);
x_342 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_343 = lean_name_mk_string(x_341, x_342);
x_344 = l___private_Init_Lean_Elab_Quotation_1__const(x_343);
if (lean_is_scalar(x_297)) {
 x_345 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_345 = x_297;
}
lean_ctor_set(x_345, 0, x_81);
lean_ctor_set(x_345, 1, x_298);
lean_ctor_set_usize(x_345, 2, x_296);
x_346 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_315);
lean_ctor_set_usize(x_346, 2, x_294);
lean_ctor_set(x_33, 0, x_346);
if (lean_is_scalar(x_314)) {
 x_347 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_347 = x_314;
}
lean_ctor_set(x_347, 0, x_33);
lean_ctor_set(x_347, 1, x_82);
lean_ctor_set_usize(x_347, 2, x_84);
x_348 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_347);
x_349 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_350 = lean_array_push(x_349, x_348);
x_351 = lean_array_push(x_350, x_338);
x_352 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_351, x_351, x_336, x_344);
lean_dec(x_351);
return x_352;
}
else
{
lean_object* x_353; uint8_t x_354; 
lean_dec(x_85);
x_353 = l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
x_354 = lean_string_dec_eq(x_82, x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_355 = lean_unsigned_to_nat(0u);
x_356 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_355, x_6);
x_357 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_356);
lean_dec(x_356);
x_358 = lean_name_mk_string(x_81, x_298);
x_359 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_360 = lean_name_mk_string(x_358, x_359);
x_361 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_362 = lean_name_mk_string(x_360, x_361);
x_363 = l___private_Init_Lean_Elab_Quotation_1__const(x_362);
if (lean_is_scalar(x_297)) {
 x_364 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_364 = x_297;
}
lean_ctor_set(x_364, 0, x_81);
lean_ctor_set(x_364, 1, x_298);
lean_ctor_set_usize(x_364, 2, x_296);
x_365 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_315);
lean_ctor_set_usize(x_365, 2, x_294);
lean_ctor_set(x_33, 1, x_334);
lean_ctor_set(x_33, 0, x_365);
if (lean_is_scalar(x_314)) {
 x_366 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_366 = x_314;
}
lean_ctor_set(x_366, 0, x_33);
lean_ctor_set(x_366, 1, x_82);
lean_ctor_set_usize(x_366, 2, x_84);
x_367 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_366);
x_368 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_369 = lean_array_push(x_368, x_367);
x_370 = lean_array_push(x_369, x_357);
x_371 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_370, x_370, x_355, x_363);
lean_dec(x_370);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_314);
lean_dec(x_297);
lean_free_object(x_33);
lean_dec(x_82);
x_372 = l_Lean_stxInh;
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_array_get(x_372, x_6, x_373);
lean_dec(x_6);
return x_374;
}
}
}
}
}
}
else
{
size_t x_375; lean_object* x_376; size_t x_377; lean_object* x_378; size_t x_379; lean_object* x_380; lean_object* x_381; size_t x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_375 = lean_ctor_get_usize(x_5, 2);
x_376 = lean_ctor_get(x_33, 1);
x_377 = lean_ctor_get_usize(x_33, 2);
lean_inc(x_376);
lean_dec(x_33);
x_378 = lean_ctor_get(x_49, 1);
lean_inc(x_378);
x_379 = lean_ctor_get_usize(x_49, 2);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_380 = x_49;
} else {
 lean_dec_ref(x_49);
 x_380 = lean_box(0);
}
x_381 = lean_ctor_get(x_65, 1);
lean_inc(x_381);
x_382 = lean_ctor_get_usize(x_65, 2);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_383 = x_65;
} else {
 lean_dec_ref(x_65);
 x_383 = lean_box(0);
}
x_384 = l_Lean_nameToExprAux___main___closed__1;
x_385 = lean_string_dec_eq(x_381, x_384);
lean_dec(x_381);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_383);
lean_dec(x_380);
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_82);
x_386 = lean_unsigned_to_nat(0u);
x_387 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(x_1, x_386, x_6);
x_388 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_387);
lean_dec(x_387);
x_389 = lean_name_mk_string(x_81, x_384);
x_390 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_391 = lean_name_mk_string(x_389, x_390);
x_392 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_393 = lean_name_mk_string(x_391, x_392);
x_394 = l___private_Init_Lean_Elab_Quotation_1__const(x_393);
x_395 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_396 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_397 = lean_array_push(x_396, x_395);
x_398 = lean_array_push(x_397, x_388);
x_399 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_398, x_398, x_386, x_394);
lean_dec(x_398);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_400 = x_5;
} else {
 lean_dec_ref(x_5);
 x_400 = lean_box(0);
}
x_401 = l_Lean_Syntax_formatStx___main___closed__5;
x_402 = lean_string_dec_eq(x_378, x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_403 = lean_unsigned_to_nat(0u);
x_404 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_403, x_6);
x_405 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_404);
lean_dec(x_404);
x_406 = lean_name_mk_string(x_81, x_384);
x_407 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_408 = lean_name_mk_string(x_406, x_407);
x_409 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_410 = lean_name_mk_string(x_408, x_409);
x_411 = l___private_Init_Lean_Elab_Quotation_1__const(x_410);
if (lean_is_scalar(x_383)) {
 x_412 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_412 = x_383;
}
lean_ctor_set(x_412, 0, x_81);
lean_ctor_set(x_412, 1, x_384);
lean_ctor_set_usize(x_412, 2, x_382);
if (lean_is_scalar(x_380)) {
 x_413 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_413 = x_380;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_378);
lean_ctor_set_usize(x_413, 2, x_379);
x_414 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_376);
lean_ctor_set_usize(x_414, 2, x_377);
if (lean_is_scalar(x_400)) {
 x_415 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_415 = x_400;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_82);
lean_ctor_set_usize(x_415, 2, x_375);
x_416 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_415);
x_417 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_418 = lean_array_push(x_417, x_416);
x_419 = lean_array_push(x_418, x_405);
x_420 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_419, x_419, x_403, x_411);
lean_dec(x_419);
return x_420;
}
else
{
lean_object* x_421; uint8_t x_422; 
lean_dec(x_378);
x_421 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_422 = lean_string_dec_eq(x_376, x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_423 = lean_unsigned_to_nat(0u);
x_424 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_423, x_6);
x_425 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_424);
lean_dec(x_424);
x_426 = lean_name_mk_string(x_81, x_384);
x_427 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_428 = lean_name_mk_string(x_426, x_427);
x_429 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_430 = lean_name_mk_string(x_428, x_429);
x_431 = l___private_Init_Lean_Elab_Quotation_1__const(x_430);
if (lean_is_scalar(x_383)) {
 x_432 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_432 = x_383;
}
lean_ctor_set(x_432, 0, x_81);
lean_ctor_set(x_432, 1, x_384);
lean_ctor_set_usize(x_432, 2, x_382);
if (lean_is_scalar(x_380)) {
 x_433 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_433 = x_380;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_401);
lean_ctor_set_usize(x_433, 2, x_379);
x_434 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_376);
lean_ctor_set_usize(x_434, 2, x_377);
if (lean_is_scalar(x_400)) {
 x_435 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_435 = x_400;
}
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_82);
lean_ctor_set_usize(x_435, 2, x_375);
x_436 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_435);
x_437 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_438 = lean_array_push(x_437, x_436);
x_439 = lean_array_push(x_438, x_425);
x_440 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_439, x_439, x_423, x_431);
lean_dec(x_439);
return x_440;
}
else
{
lean_object* x_441; uint8_t x_442; 
lean_dec(x_376);
x_441 = l_Lean_Parser_Term_antiquot___elambda__1___rarg___closed__1;
x_442 = lean_string_dec_eq(x_82, x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_443 = lean_unsigned_to_nat(0u);
x_444 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_443, x_6);
x_445 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_444);
lean_dec(x_444);
x_446 = lean_name_mk_string(x_81, x_384);
x_447 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1;
x_448 = lean_name_mk_string(x_446, x_447);
x_449 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3;
x_450 = lean_name_mk_string(x_448, x_449);
x_451 = l___private_Init_Lean_Elab_Quotation_1__const(x_450);
if (lean_is_scalar(x_383)) {
 x_452 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_452 = x_383;
}
lean_ctor_set(x_452, 0, x_81);
lean_ctor_set(x_452, 1, x_384);
lean_ctor_set_usize(x_452, 2, x_382);
if (lean_is_scalar(x_380)) {
 x_453 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_453 = x_380;
}
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_401);
lean_ctor_set_usize(x_453, 2, x_379);
x_454 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_421);
lean_ctor_set_usize(x_454, 2, x_377);
if (lean_is_scalar(x_400)) {
 x_455 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_455 = x_400;
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_82);
lean_ctor_set_usize(x_455, 2, x_375);
x_456 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_455);
x_457 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_458 = lean_array_push(x_457, x_456);
x_459 = lean_array_push(x_458, x_445);
x_460 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_459, x_459, x_443, x_451);
lean_dec(x_459);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_400);
lean_dec(x_383);
lean_dec(x_380);
lean_dec(x_82);
x_461 = l_Lean_stxInh;
x_462 = lean_unsigned_to_nat(1u);
x_463 = lean_array_get(x_461, x_6, x_462);
lean_dec(x_6);
return x_463;
}
}
}
}
}
}
else
{
lean_object* x_464; 
lean_dec(x_81);
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_33);
x_464 = lean_box(0);
x_7 = x_464;
goto block_17;
}
}
default: 
{
lean_object* x_465; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_33);
x_465 = lean_box(0);
x_7 = x_465;
goto block_17;
}
}
}
default: 
{
lean_object* x_466; 
lean_dec(x_49);
lean_dec(x_33);
x_466 = lean_box(0);
x_7 = x_466;
goto block_17;
}
}
}
default: 
{
lean_object* x_467; 
lean_dec(x_33);
x_467 = lean_box(0);
x_7 = x_467;
goto block_17;
}
}
}
default: 
{
lean_object* x_468; 
x_468 = lean_box(0);
x_7 = x_468;
goto block_17;
}
}
block_17:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1(x_1, x_8, x_6);
x_10 = l___private_Init_Lean_Elab_Quotation_6__quoteArray(x_9);
lean_dec(x_9);
x_11 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_5);
x_12 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_array_push(x_13, x_10);
x_15 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5;
x_16 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_14, x_14, x_8, x_15);
lean_dec(x_14);
return x_16;
}
}
case 2:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_469 = lean_ctor_get(x_2, 1);
lean_inc(x_469);
lean_dec(x_2);
x_470 = lean_box(0);
x_471 = l_Lean_strLitKind;
x_472 = l_Lean_mkStxLit(x_471, x_469, x_470);
x_473 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13;
x_474 = lean_array_push(x_473, x_472);
x_475 = lean_unsigned_to_nat(0u);
x_476 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8;
x_477 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_474, x_474, x_475, x_476);
lean_dec(x_474);
return x_477;
}
default: 
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_478 = lean_ctor_get(x_2, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_2, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_2, 3);
lean_inc(x_480);
lean_dec(x_2);
x_481 = lean_box(0);
x_482 = lean_box(0);
lean_inc(x_479);
x_483 = l_Lean_Elab_resolveGlobalName(x_1, x_482, x_481, x_479);
x_484 = l_List_append___rarg(x_483, x_480);
x_485 = lean_box(0);
x_486 = l___private_Init_Lean_Elab_Quotation_4__quoteName___main(x_479);
x_487 = l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11(x_485, x_484);
x_488 = l___private_Init_Lean_Elab_Quotation_5__quoteList___main(x_487);
x_489 = lean_ctor_get(x_478, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_478, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_478, 2);
lean_inc(x_491);
lean_dec(x_478);
x_492 = lean_string_utf8_extract(x_489, x_490, x_491);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
x_493 = l_Lean_strLitKind;
x_494 = l_Lean_mkStxLit(x_493, x_492, x_485);
x_495 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18;
x_496 = l___private_Init_Lean_Elab_Quotation_2__app(x_495, x_494);
x_497 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19;
x_498 = lean_array_push(x_497, x_496);
x_499 = lean_array_push(x_498, x_486);
x_500 = lean_array_push(x_499, x_488);
x_501 = lean_unsigned_to_nat(0u);
x_502 = l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15;
x_503 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Quotation_3__appN___spec__1(x_500, x_500, x_501, x_502);
lean_dec(x_500);
return x_503;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_7__quote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Quotation_7__quote(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_stxQuot_expand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasPure");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_stxQuot_expand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_stxQuot_expand___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_stxQuot_expand___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pure");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_stxQuot_expand___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_stxQuot_expand___closed__2;
x_2 = l_Lean_Elab_stxQuot_expand___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_stxQuot_expand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_stxQuot_expand___closed__4;
x_2 = l___private_Init_Lean_Elab_Quotation_1__const(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_stxQuot_expand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_4);
x_6 = l_Lean_Elab_stxQuot_expand___closed__5;
x_7 = l___private_Init_Lean_Elab_Quotation_2__app(x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_stxQuot_expand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_stxQuot_expand(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Inhabited;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stxQuot: unimplemented kind ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Elab.Quotation");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_Lean_mkStrLit(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stxQuot: unimplemented: projection notation");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_getArgs(x_2);
x_4 = l_Lean_Syntax_getKind(x_2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = l_Lean_strLitKind___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_numLitKind___closed__1;
x_22 = lean_string_dec_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_box(0);
x_5 = x_23;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_24 = l_Lean_numLitKind;
x_25 = l_Lean_Syntax_isNatLitAux(x_24, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5;
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_mkNatLit(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_4);
x_30 = l_Lean_Syntax_isStrLit(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7;
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_mkStrLit(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
case 1:
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
size_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get_usize(x_4, 2);
x_41 = lean_ctor_get(x_17, 1);
x_42 = lean_ctor_get(x_17, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_35, 1);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_36, 1);
x_48 = lean_ctor_get(x_36, 0);
lean_dec(x_48);
x_49 = l_Lean_nameToExprAux___main___closed__1;
x_50 = lean_string_dec_eq(x_47, x_49);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_dec(x_44);
lean_free_object(x_17);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_3);
x_51 = lean_box(0);
x_5 = x_51;
goto block_16;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_4, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_4, 0);
lean_dec(x_54);
x_55 = l_Lean_Syntax_formatStx___main___closed__5;
x_56 = lean_string_dec_eq(x_44, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
x_57 = l_System_FilePath_dirName___closed__1;
x_58 = l_Lean_Name_toStringWithSep___main(x_57, x_4);
x_59 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_62 = lean_unsigned_to_nat(93u);
x_63 = lean_unsigned_to_nat(9u);
x_64 = l___private_Init_Util_1__mkPanicMessage(x_61, x_62, x_63, x_60);
lean_dec(x_60);
x_65 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_66 = lean_panic_fn(x_64);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_44);
x_67 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_68 = lean_string_dec_eq(x_41, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
lean_ctor_set(x_35, 1, x_55);
x_69 = l_System_FilePath_dirName___closed__1;
x_70 = l_Lean_Name_toStringWithSep___main(x_69, x_4);
x_71 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_74 = lean_unsigned_to_nat(93u);
x_75 = lean_unsigned_to_nat(9u);
x_76 = l___private_Init_Util_1__mkPanicMessage(x_73, x_74, x_75, x_72);
lean_dec(x_72);
x_77 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_78 = lean_panic_fn(x_76);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_41);
x_79 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_80 = lean_string_dec_eq(x_38, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_82 = lean_string_dec_eq(x_38, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_84 = lean_string_dec_eq(x_38, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
lean_ctor_set(x_35, 1, x_55);
lean_ctor_set(x_17, 1, x_67);
x_85 = l_System_FilePath_dirName___closed__1;
x_86 = l_Lean_Name_toStringWithSep___main(x_85, x_4);
x_87 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_90 = lean_unsigned_to_nat(93u);
x_91 = lean_unsigned_to_nat(9u);
x_92 = l___private_Init_Util_1__mkPanicMessage(x_89, x_90, x_91, x_88);
lean_dec(x_88);
x_93 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_94 = lean_panic_fn(x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_4);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_95 = l_Lean_stxInh;
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_array_get(x_95, x_3, x_96);
lean_dec(x_3);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_Syntax_getArg(x_97, x_98);
lean_dec(x_97);
x_2 = x_99;
goto _start;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_4);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_101 = l_Lean_stxInh;
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_array_get(x_101, x_3, x_102);
x_104 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
return x_104;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_array_get(x_101, x_3, x_109);
lean_dec(x_3);
x_111 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_108);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = l_Lean_mkApp(x_108, x_116);
lean_ctor_set(x_111, 0, x_117);
return x_111;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
lean_dec(x_111);
x_119 = l_Lean_mkApp(x_108, x_118);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_4);
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_121 = l_Lean_stxInh;
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_array_get(x_121, x_3, x_122);
lean_dec(x_3);
if (lean_obj_tag(x_123) == 3)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 3);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_box(0);
lean_inc(x_124);
x_127 = l_Lean_Elab_resolveGlobalName(x_1, x_37, x_126, x_124);
x_128 = l_List_append___rarg(x_127, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = l_Lean_mkFVar(x_124);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_124);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_mkConst(x_133, x_126);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_131);
x_136 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_123);
x_137 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_138 = l_unreachable_x21___rarg(x_137);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_4);
x_139 = l_Lean_Syntax_formatStx___main___closed__5;
x_140 = lean_string_dec_eq(x_44, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
x_141 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_141, 0, x_17);
lean_ctor_set(x_141, 1, x_38);
lean_ctor_set_usize(x_141, 2, x_40);
x_142 = l_System_FilePath_dirName___closed__1;
x_143 = l_Lean_Name_toStringWithSep___main(x_142, x_141);
x_144 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_145 = lean_string_append(x_144, x_143);
lean_dec(x_143);
x_146 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_147 = lean_unsigned_to_nat(93u);
x_148 = lean_unsigned_to_nat(9u);
x_149 = l___private_Init_Util_1__mkPanicMessage(x_146, x_147, x_148, x_145);
lean_dec(x_145);
x_150 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_151 = lean_panic_fn(x_149);
return x_151;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_44);
x_152 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_153 = lean_string_dec_eq(x_41, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
lean_ctor_set(x_35, 1, x_139);
x_154 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_154, 0, x_17);
lean_ctor_set(x_154, 1, x_38);
lean_ctor_set_usize(x_154, 2, x_40);
x_155 = l_System_FilePath_dirName___closed__1;
x_156 = l_Lean_Name_toStringWithSep___main(x_155, x_154);
x_157 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_158 = lean_string_append(x_157, x_156);
lean_dec(x_156);
x_159 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_160 = lean_unsigned_to_nat(93u);
x_161 = lean_unsigned_to_nat(9u);
x_162 = l___private_Init_Util_1__mkPanicMessage(x_159, x_160, x_161, x_158);
lean_dec(x_158);
x_163 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_164 = lean_panic_fn(x_162);
return x_164;
}
else
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_41);
x_165 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_166 = lean_string_dec_eq(x_38, x_165);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_168 = lean_string_dec_eq(x_38, x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_170 = lean_string_dec_eq(x_38, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_3);
lean_ctor_set(x_36, 1, x_49);
lean_ctor_set(x_35, 1, x_139);
lean_ctor_set(x_17, 1, x_152);
x_171 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_171, 0, x_17);
lean_ctor_set(x_171, 1, x_38);
lean_ctor_set_usize(x_171, 2, x_40);
x_172 = l_System_FilePath_dirName___closed__1;
x_173 = l_Lean_Name_toStringWithSep___main(x_172, x_171);
x_174 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_175 = lean_string_append(x_174, x_173);
lean_dec(x_173);
x_176 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_177 = lean_unsigned_to_nat(93u);
x_178 = lean_unsigned_to_nat(9u);
x_179 = l___private_Init_Util_1__mkPanicMessage(x_176, x_177, x_178, x_175);
lean_dec(x_175);
x_180 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_181 = lean_panic_fn(x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_182 = l_Lean_stxInh;
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_array_get(x_182, x_3, x_183);
lean_dec(x_3);
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Lean_Syntax_getArg(x_184, x_185);
lean_dec(x_184);
x_2 = x_186;
goto _start;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_188 = l_Lean_stxInh;
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_array_get(x_188, x_3, x_189);
x_191 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_3);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_191, 0);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_array_get(x_188, x_3, x_196);
lean_dec(x_3);
x_198 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_195);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
x_204 = l_Lean_mkApp(x_195, x_202);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_free_object(x_36);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_206 = l_Lean_stxInh;
x_207 = lean_unsigned_to_nat(0u);
x_208 = lean_array_get(x_206, x_3, x_207);
lean_dec(x_3);
if (lean_obj_tag(x_208) == 3)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_208, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 3);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_box(0);
lean_inc(x_209);
x_212 = l_Lean_Elab_resolveGlobalName(x_1, x_37, x_211, x_209);
x_213 = l_List_append___rarg(x_212, x_210);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = l_Lean_mkFVar(x_209);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_209);
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_mkConst(x_218, x_211);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
else
{
lean_object* x_221; 
lean_dec(x_217);
lean_dec(x_216);
x_221 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_208);
x_222 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_223 = l_unreachable_x21___rarg(x_222);
return x_223;
}
}
}
}
}
}
}
else
{
lean_object* x_224; size_t x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_36, 1);
x_225 = lean_ctor_get_usize(x_36, 2);
lean_inc(x_224);
lean_dec(x_36);
x_226 = l_Lean_nameToExprAux___main___closed__1;
x_227 = lean_string_dec_eq(x_224, x_226);
lean_dec(x_224);
if (x_227 == 0)
{
lean_object* x_228; 
lean_free_object(x_35);
lean_dec(x_44);
lean_free_object(x_17);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_3);
x_228 = lean_box(0);
x_5 = x_228;
goto block_16;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_229 = x_4;
} else {
 lean_dec_ref(x_4);
 x_229 = lean_box(0);
}
x_230 = l_Lean_Syntax_formatStx___main___closed__5;
x_231 = lean_string_dec_eq(x_44, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_3);
x_232 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_232, 0, x_37);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set_usize(x_232, 2, x_225);
lean_ctor_set(x_35, 0, x_232);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_233 = x_229;
}
lean_ctor_set(x_233, 0, x_17);
lean_ctor_set(x_233, 1, x_38);
lean_ctor_set_usize(x_233, 2, x_40);
x_234 = l_System_FilePath_dirName___closed__1;
x_235 = l_Lean_Name_toStringWithSep___main(x_234, x_233);
x_236 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_237 = lean_string_append(x_236, x_235);
lean_dec(x_235);
x_238 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_239 = lean_unsigned_to_nat(93u);
x_240 = lean_unsigned_to_nat(9u);
x_241 = l___private_Init_Util_1__mkPanicMessage(x_238, x_239, x_240, x_237);
lean_dec(x_237);
x_242 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_243 = lean_panic_fn(x_241);
return x_243;
}
else
{
lean_object* x_244; uint8_t x_245; 
lean_dec(x_44);
x_244 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_245 = lean_string_dec_eq(x_41, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_3);
x_246 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_246, 0, x_37);
lean_ctor_set(x_246, 1, x_226);
lean_ctor_set_usize(x_246, 2, x_225);
lean_ctor_set(x_35, 1, x_230);
lean_ctor_set(x_35, 0, x_246);
if (lean_is_scalar(x_229)) {
 x_247 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_247 = x_229;
}
lean_ctor_set(x_247, 0, x_17);
lean_ctor_set(x_247, 1, x_38);
lean_ctor_set_usize(x_247, 2, x_40);
x_248 = l_System_FilePath_dirName___closed__1;
x_249 = l_Lean_Name_toStringWithSep___main(x_248, x_247);
x_250 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_251 = lean_string_append(x_250, x_249);
lean_dec(x_249);
x_252 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_253 = lean_unsigned_to_nat(93u);
x_254 = lean_unsigned_to_nat(9u);
x_255 = l___private_Init_Util_1__mkPanicMessage(x_252, x_253, x_254, x_251);
lean_dec(x_251);
x_256 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_257 = lean_panic_fn(x_255);
return x_257;
}
else
{
lean_object* x_258; uint8_t x_259; 
lean_dec(x_41);
x_258 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_259 = lean_string_dec_eq(x_38, x_258);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_261 = lean_string_dec_eq(x_38, x_260);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_263 = lean_string_dec_eq(x_38, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_3);
x_264 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_264, 0, x_37);
lean_ctor_set(x_264, 1, x_226);
lean_ctor_set_usize(x_264, 2, x_225);
lean_ctor_set(x_35, 1, x_230);
lean_ctor_set(x_35, 0, x_264);
lean_ctor_set(x_17, 1, x_244);
if (lean_is_scalar(x_229)) {
 x_265 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_265 = x_229;
}
lean_ctor_set(x_265, 0, x_17);
lean_ctor_set(x_265, 1, x_38);
lean_ctor_set_usize(x_265, 2, x_40);
x_266 = l_System_FilePath_dirName___closed__1;
x_267 = l_Lean_Name_toStringWithSep___main(x_266, x_265);
x_268 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_269 = lean_string_append(x_268, x_267);
lean_dec(x_267);
x_270 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_271 = lean_unsigned_to_nat(93u);
x_272 = lean_unsigned_to_nat(9u);
x_273 = l___private_Init_Util_1__mkPanicMessage(x_270, x_271, x_272, x_269);
lean_dec(x_269);
x_274 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_275 = lean_panic_fn(x_273);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_229);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_276 = l_Lean_stxInh;
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_array_get(x_276, x_3, x_277);
lean_dec(x_3);
x_279 = lean_unsigned_to_nat(0u);
x_280 = l_Lean_Syntax_getArg(x_278, x_279);
lean_dec(x_278);
x_2 = x_280;
goto _start;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_229);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_282 = l_Lean_stxInh;
x_283 = lean_unsigned_to_nat(0u);
x_284 = lean_array_get(x_282, x_3, x_283);
x_285 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_3);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
lean_dec(x_285);
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_array_get(x_282, x_3, x_290);
lean_dec(x_3);
x_292 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_289);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(0, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_297 = x_292;
} else {
 lean_dec_ref(x_292);
 x_297 = lean_box(0);
}
x_298 = l_Lean_mkApp(x_289, x_296);
if (lean_is_scalar(x_297)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_297;
}
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_229);
lean_free_object(x_35);
lean_free_object(x_17);
lean_dec(x_38);
x_300 = l_Lean_stxInh;
x_301 = lean_unsigned_to_nat(0u);
x_302 = lean_array_get(x_300, x_3, x_301);
lean_dec(x_3);
if (lean_obj_tag(x_302) == 3)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_302, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 3);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_box(0);
lean_inc(x_303);
x_306 = l_Lean_Elab_resolveGlobalName(x_1, x_37, x_305, x_303);
x_307 = l_List_append___rarg(x_306, x_304);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = l_Lean_mkFVar(x_303);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_303);
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_mkConst(x_312, x_305);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
else
{
lean_object* x_315; 
lean_dec(x_311);
lean_dec(x_310);
x_315 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_302);
x_316 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_317 = l_unreachable_x21___rarg(x_316);
return x_317;
}
}
}
}
}
}
}
else
{
lean_object* x_318; size_t x_319; lean_object* x_320; size_t x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_318 = lean_ctor_get(x_35, 1);
x_319 = lean_ctor_get_usize(x_35, 2);
lean_inc(x_318);
lean_dec(x_35);
x_320 = lean_ctor_get(x_36, 1);
lean_inc(x_320);
x_321 = lean_ctor_get_usize(x_36, 2);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_322 = x_36;
} else {
 lean_dec_ref(x_36);
 x_322 = lean_box(0);
}
x_323 = l_Lean_nameToExprAux___main___closed__1;
x_324 = lean_string_dec_eq(x_320, x_323);
lean_dec(x_320);
if (x_324 == 0)
{
lean_object* x_325; 
lean_dec(x_322);
lean_dec(x_318);
lean_free_object(x_17);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_3);
x_325 = lean_box(0);
x_5 = x_325;
goto block_16;
}
else
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_326 = x_4;
} else {
 lean_dec_ref(x_4);
 x_326 = lean_box(0);
}
x_327 = l_Lean_Syntax_formatStx___main___closed__5;
x_328 = lean_string_dec_eq(x_318, x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_3);
if (lean_is_scalar(x_322)) {
 x_329 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_329 = x_322;
}
lean_ctor_set(x_329, 0, x_37);
lean_ctor_set(x_329, 1, x_323);
lean_ctor_set_usize(x_329, 2, x_321);
x_330 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_318);
lean_ctor_set_usize(x_330, 2, x_319);
lean_ctor_set(x_17, 0, x_330);
if (lean_is_scalar(x_326)) {
 x_331 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_331 = x_326;
}
lean_ctor_set(x_331, 0, x_17);
lean_ctor_set(x_331, 1, x_38);
lean_ctor_set_usize(x_331, 2, x_40);
x_332 = l_System_FilePath_dirName___closed__1;
x_333 = l_Lean_Name_toStringWithSep___main(x_332, x_331);
x_334 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_335 = lean_string_append(x_334, x_333);
lean_dec(x_333);
x_336 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_337 = lean_unsigned_to_nat(93u);
x_338 = lean_unsigned_to_nat(9u);
x_339 = l___private_Init_Util_1__mkPanicMessage(x_336, x_337, x_338, x_335);
lean_dec(x_335);
x_340 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_341 = lean_panic_fn(x_339);
return x_341;
}
else
{
lean_object* x_342; uint8_t x_343; 
lean_dec(x_318);
x_342 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_343 = lean_string_dec_eq(x_41, x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_3);
if (lean_is_scalar(x_322)) {
 x_344 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_344 = x_322;
}
lean_ctor_set(x_344, 0, x_37);
lean_ctor_set(x_344, 1, x_323);
lean_ctor_set_usize(x_344, 2, x_321);
x_345 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_327);
lean_ctor_set_usize(x_345, 2, x_319);
lean_ctor_set(x_17, 0, x_345);
if (lean_is_scalar(x_326)) {
 x_346 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_346 = x_326;
}
lean_ctor_set(x_346, 0, x_17);
lean_ctor_set(x_346, 1, x_38);
lean_ctor_set_usize(x_346, 2, x_40);
x_347 = l_System_FilePath_dirName___closed__1;
x_348 = l_Lean_Name_toStringWithSep___main(x_347, x_346);
x_349 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_350 = lean_string_append(x_349, x_348);
lean_dec(x_348);
x_351 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_352 = lean_unsigned_to_nat(93u);
x_353 = lean_unsigned_to_nat(9u);
x_354 = l___private_Init_Util_1__mkPanicMessage(x_351, x_352, x_353, x_350);
lean_dec(x_350);
x_355 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_356 = lean_panic_fn(x_354);
return x_356;
}
else
{
lean_object* x_357; uint8_t x_358; 
lean_dec(x_41);
x_357 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_358 = lean_string_dec_eq(x_38, x_357);
if (x_358 == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_360 = lean_string_dec_eq(x_38, x_359);
if (x_360 == 0)
{
lean_object* x_361; uint8_t x_362; 
x_361 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_362 = lean_string_dec_eq(x_38, x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_3);
if (lean_is_scalar(x_322)) {
 x_363 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_363 = x_322;
}
lean_ctor_set(x_363, 0, x_37);
lean_ctor_set(x_363, 1, x_323);
lean_ctor_set_usize(x_363, 2, x_321);
x_364 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_327);
lean_ctor_set_usize(x_364, 2, x_319);
lean_ctor_set(x_17, 1, x_342);
lean_ctor_set(x_17, 0, x_364);
if (lean_is_scalar(x_326)) {
 x_365 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_365 = x_326;
}
lean_ctor_set(x_365, 0, x_17);
lean_ctor_set(x_365, 1, x_38);
lean_ctor_set_usize(x_365, 2, x_40);
x_366 = l_System_FilePath_dirName___closed__1;
x_367 = l_Lean_Name_toStringWithSep___main(x_366, x_365);
x_368 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_369 = lean_string_append(x_368, x_367);
lean_dec(x_367);
x_370 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_371 = lean_unsigned_to_nat(93u);
x_372 = lean_unsigned_to_nat(9u);
x_373 = l___private_Init_Util_1__mkPanicMessage(x_370, x_371, x_372, x_369);
lean_dec(x_369);
x_374 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_375 = lean_panic_fn(x_373);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_326);
lean_dec(x_322);
lean_free_object(x_17);
lean_dec(x_38);
x_376 = l_Lean_stxInh;
x_377 = lean_unsigned_to_nat(1u);
x_378 = lean_array_get(x_376, x_3, x_377);
lean_dec(x_3);
x_379 = lean_unsigned_to_nat(0u);
x_380 = l_Lean_Syntax_getArg(x_378, x_379);
lean_dec(x_378);
x_2 = x_380;
goto _start;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_326);
lean_dec(x_322);
lean_free_object(x_17);
lean_dec(x_38);
x_382 = l_Lean_stxInh;
x_383 = lean_unsigned_to_nat(0u);
x_384 = lean_array_get(x_382, x_3, x_383);
x_385 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_3);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_387 = x_385;
} else {
 lean_dec_ref(x_385);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(0, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
lean_dec(x_385);
x_390 = lean_unsigned_to_nat(1u);
x_391 = lean_array_get(x_382, x_3, x_390);
lean_dec(x_3);
x_392 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_389);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_394 = x_392;
} else {
 lean_dec_ref(x_392);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(0, 1, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_393);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_396 = lean_ctor_get(x_392, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_397 = x_392;
} else {
 lean_dec_ref(x_392);
 x_397 = lean_box(0);
}
x_398 = l_Lean_mkApp(x_389, x_396);
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_398);
return x_399;
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_326);
lean_dec(x_322);
lean_free_object(x_17);
lean_dec(x_38);
x_400 = l_Lean_stxInh;
x_401 = lean_unsigned_to_nat(0u);
x_402 = lean_array_get(x_400, x_3, x_401);
lean_dec(x_3);
if (lean_obj_tag(x_402) == 3)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_402, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 3);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_box(0);
lean_inc(x_403);
x_406 = l_Lean_Elab_resolveGlobalName(x_1, x_37, x_405, x_403);
x_407 = l_List_append___rarg(x_406, x_404);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = l_Lean_mkFVar(x_403);
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_408);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_403);
x_410 = lean_ctor_get(x_407, 0);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Lean_mkConst(x_412, x_405);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_413);
return x_414;
}
else
{
lean_object* x_415; 
lean_dec(x_411);
lean_dec(x_410);
x_415 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
return x_415;
}
}
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_402);
x_416 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_417 = l_unreachable_x21___rarg(x_416);
return x_417;
}
}
}
}
}
}
}
else
{
size_t x_418; lean_object* x_419; size_t x_420; lean_object* x_421; size_t x_422; lean_object* x_423; lean_object* x_424; size_t x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_418 = lean_ctor_get_usize(x_4, 2);
x_419 = lean_ctor_get(x_17, 1);
x_420 = lean_ctor_get_usize(x_17, 2);
lean_inc(x_419);
lean_dec(x_17);
x_421 = lean_ctor_get(x_35, 1);
lean_inc(x_421);
x_422 = lean_ctor_get_usize(x_35, 2);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_423 = x_35;
} else {
 lean_dec_ref(x_35);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_36, 1);
lean_inc(x_424);
x_425 = lean_ctor_get_usize(x_36, 2);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_426 = x_36;
} else {
 lean_dec_ref(x_36);
 x_426 = lean_box(0);
}
x_427 = l_Lean_nameToExprAux___main___closed__1;
x_428 = lean_string_dec_eq(x_424, x_427);
lean_dec(x_424);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_426);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_38);
lean_dec(x_3);
x_429 = lean_box(0);
x_5 = x_429;
goto block_16;
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_430 = x_4;
} else {
 lean_dec_ref(x_4);
 x_430 = lean_box(0);
}
x_431 = l_Lean_Syntax_formatStx___main___closed__5;
x_432 = lean_string_dec_eq(x_421, x_431);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_3);
if (lean_is_scalar(x_426)) {
 x_433 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_433 = x_426;
}
lean_ctor_set(x_433, 0, x_37);
lean_ctor_set(x_433, 1, x_427);
lean_ctor_set_usize(x_433, 2, x_425);
if (lean_is_scalar(x_423)) {
 x_434 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_434 = x_423;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_421);
lean_ctor_set_usize(x_434, 2, x_422);
x_435 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_419);
lean_ctor_set_usize(x_435, 2, x_420);
if (lean_is_scalar(x_430)) {
 x_436 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_436 = x_430;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_38);
lean_ctor_set_usize(x_436, 2, x_418);
x_437 = l_System_FilePath_dirName___closed__1;
x_438 = l_Lean_Name_toStringWithSep___main(x_437, x_436);
x_439 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_440 = lean_string_append(x_439, x_438);
lean_dec(x_438);
x_441 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_442 = lean_unsigned_to_nat(93u);
x_443 = lean_unsigned_to_nat(9u);
x_444 = l___private_Init_Util_1__mkPanicMessage(x_441, x_442, x_443, x_440);
lean_dec(x_440);
x_445 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_446 = lean_panic_fn(x_444);
return x_446;
}
else
{
lean_object* x_447; uint8_t x_448; 
lean_dec(x_421);
x_447 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_448 = lean_string_dec_eq(x_419, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_3);
if (lean_is_scalar(x_426)) {
 x_449 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_449 = x_426;
}
lean_ctor_set(x_449, 0, x_37);
lean_ctor_set(x_449, 1, x_427);
lean_ctor_set_usize(x_449, 2, x_425);
if (lean_is_scalar(x_423)) {
 x_450 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_450 = x_423;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_431);
lean_ctor_set_usize(x_450, 2, x_422);
x_451 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_419);
lean_ctor_set_usize(x_451, 2, x_420);
if (lean_is_scalar(x_430)) {
 x_452 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_452 = x_430;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_38);
lean_ctor_set_usize(x_452, 2, x_418);
x_453 = l_System_FilePath_dirName___closed__1;
x_454 = l_Lean_Name_toStringWithSep___main(x_453, x_452);
x_455 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_456 = lean_string_append(x_455, x_454);
lean_dec(x_454);
x_457 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_458 = lean_unsigned_to_nat(93u);
x_459 = lean_unsigned_to_nat(9u);
x_460 = l___private_Init_Util_1__mkPanicMessage(x_457, x_458, x_459, x_456);
lean_dec(x_456);
x_461 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_462 = lean_panic_fn(x_460);
return x_462;
}
else
{
lean_object* x_463; uint8_t x_464; 
lean_dec(x_419);
x_463 = l_Lean_Parser_Term_id___elambda__1___closed__1;
x_464 = lean_string_dec_eq(x_38, x_463);
if (x_464 == 0)
{
lean_object* x_465; uint8_t x_466; 
x_465 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_466 = lean_string_dec_eq(x_38, x_465);
if (x_466 == 0)
{
lean_object* x_467; uint8_t x_468; 
x_467 = l_Lean_Parser_Level_paren___elambda__1___rarg___closed__3;
x_468 = lean_string_dec_eq(x_38, x_467);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_3);
if (lean_is_scalar(x_426)) {
 x_469 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_469 = x_426;
}
lean_ctor_set(x_469, 0, x_37);
lean_ctor_set(x_469, 1, x_427);
lean_ctor_set_usize(x_469, 2, x_425);
if (lean_is_scalar(x_423)) {
 x_470 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_470 = x_423;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_431);
lean_ctor_set_usize(x_470, 2, x_422);
x_471 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_447);
lean_ctor_set_usize(x_471, 2, x_420);
if (lean_is_scalar(x_430)) {
 x_472 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_472 = x_430;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_38);
lean_ctor_set_usize(x_472, 2, x_418);
x_473 = l_System_FilePath_dirName___closed__1;
x_474 = l_Lean_Name_toStringWithSep___main(x_473, x_472);
x_475 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_476 = lean_string_append(x_475, x_474);
lean_dec(x_474);
x_477 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_478 = lean_unsigned_to_nat(93u);
x_479 = lean_unsigned_to_nat(9u);
x_480 = l___private_Init_Util_1__mkPanicMessage(x_477, x_478, x_479, x_476);
lean_dec(x_476);
x_481 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_482 = lean_panic_fn(x_480);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_430);
lean_dec(x_426);
lean_dec(x_423);
lean_dec(x_38);
x_483 = l_Lean_stxInh;
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_array_get(x_483, x_3, x_484);
lean_dec(x_3);
x_486 = lean_unsigned_to_nat(0u);
x_487 = l_Lean_Syntax_getArg(x_485, x_486);
lean_dec(x_485);
x_2 = x_487;
goto _start;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_430);
lean_dec(x_426);
lean_dec(x_423);
lean_dec(x_38);
x_489 = l_Lean_stxInh;
x_490 = lean_unsigned_to_nat(0u);
x_491 = lean_array_get(x_489, x_3, x_490);
x_492 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_491);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_3);
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_496 = lean_ctor_get(x_492, 0);
lean_inc(x_496);
lean_dec(x_492);
x_497 = lean_unsigned_to_nat(1u);
x_498 = lean_array_get(x_489, x_3, x_497);
lean_dec(x_3);
x_499 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_498);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_496);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 x_501 = x_499;
} else {
 lean_dec_ref(x_499);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(0, 1, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_500);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_503 = lean_ctor_get(x_499, 0);
lean_inc(x_503);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 x_504 = x_499;
} else {
 lean_dec_ref(x_499);
 x_504 = lean_box(0);
}
x_505 = l_Lean_mkApp(x_496, x_503);
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_504;
}
lean_ctor_set(x_506, 0, x_505);
return x_506;
}
}
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_430);
lean_dec(x_426);
lean_dec(x_423);
lean_dec(x_38);
x_507 = l_Lean_stxInh;
x_508 = lean_unsigned_to_nat(0u);
x_509 = lean_array_get(x_507, x_3, x_508);
lean_dec(x_3);
if (lean_obj_tag(x_509) == 3)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_510 = lean_ctor_get(x_509, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 3);
lean_inc(x_511);
lean_dec(x_509);
x_512 = lean_box(0);
lean_inc(x_510);
x_513 = l_Lean_Elab_resolveGlobalName(x_1, x_37, x_512, x_510);
x_514 = l_List_append___rarg(x_513, x_511);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = l_Lean_mkFVar(x_510);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; 
lean_dec(x_510);
x_517 = lean_ctor_get(x_514, 0);
lean_inc(x_517);
lean_dec(x_514);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_517, 0);
lean_inc(x_519);
lean_dec(x_517);
x_520 = l_Lean_mkConst(x_519, x_512);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
lean_object* x_522; 
lean_dec(x_518);
lean_dec(x_517);
x_522 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9;
return x_522;
}
}
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_509);
x_523 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_524 = l_unreachable_x21___rarg(x_523);
return x_524;
}
}
}
}
}
}
}
else
{
lean_object* x_525; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_3);
x_525 = lean_box(0);
x_5 = x_525;
goto block_16;
}
}
else
{
lean_object* x_526; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_3);
x_526 = lean_box(0);
x_5 = x_526;
goto block_16;
}
}
else
{
lean_object* x_527; 
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_3);
x_527 = lean_box(0);
x_5 = x_527;
goto block_16;
}
}
default: 
{
lean_object* x_528; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_528 = lean_box(0);
x_5 = x_528;
goto block_16;
}
}
}
else
{
lean_object* x_529; 
lean_dec(x_3);
lean_dec(x_2);
x_529 = lean_box(0);
x_5 = x_529;
goto block_16;
}
block_16:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3;
x_11 = lean_unsigned_to_nat(93u);
x_12 = lean_unsigned_to_nat(9u);
x_13 = l___private_Init_Util_1__mkPanicMessage(x_10, x_11, x_12, x_9);
lean_dec(x_9);
x_14 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1;
x_15 = lean_panic_fn(x_13);
return x_15;
}
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Quotation_8__toPreterm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Quotation_8__toPreterm(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_oldParseStxQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<foo>");
return x_1;
}
}
lean_object* lean_parse_stx_quot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = l_Lean_Elab_oldParseStxQuot___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Parser_mkParserContextCore(x_1, x_2, x_4);
lean_inc(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_mkParserState(x_2);
lean_dec(x_2);
x_8 = l_Lean_Parser_ParserState_setPos(x_7, x_3);
x_9 = l_Lean_Parser_termParserAttribute;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Parser_ParserAttribute_runParser(x_9, x_10, x_6, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 3);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_12);
lean_dec(x_12);
x_16 = l___private_Init_Lean_Elab_Quotation_7__quote___main(x_1, x_15);
x_17 = l_Lean_Elab_stxQuot_expand___closed__5;
x_18 = l___private_Init_Lean_Elab_Quotation_2__app(x_17, x_16);
x_19 = l___private_Init_Lean_Elab_Quotation_8__toPreterm___main(x_1, x_18);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Lean_Parser_Error_toString(x_31);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_19);
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_33);
lean_dec(x_14);
x_34 = l_Lean_Parser_Error_toString(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
lean_object* initialize_Init_Lean_Syntax(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Parser(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1 = _init_l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__1);
l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2 = _init_l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_4__quoteName___main___closed__2);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__1);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__2);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__3);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__4);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__5);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__6);
l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7 = _init_l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_5__quoteList___main___closed__7);
l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1 = _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__1);
l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2 = _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__2);
l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3 = _init_l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_6__quoteArray___closed__3);
l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1 = _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1();
lean_mark_persistent(l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__1);
l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2 = _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2();
lean_mark_persistent(l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__2);
l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3 = _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3();
lean_mark_persistent(l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__3);
l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4 = _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4();
lean_mark_persistent(l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__4);
l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5 = _init_l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5();
lean_mark_persistent(l_List_map___main___at___private_Init_Lean_Elab_Quotation_7__quote___main___spec__11___closed__5);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__1);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__2);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__3);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__4);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__5);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__6);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__7);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__8);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__9);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__10);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__11);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__12);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__13);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__14);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__15);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__16);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__17);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__18);
l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19 = _init_l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_7__quote___main___closed__19);
l_Lean_Elab_stxQuot_expand___closed__1 = _init_l_Lean_Elab_stxQuot_expand___closed__1();
lean_mark_persistent(l_Lean_Elab_stxQuot_expand___closed__1);
l_Lean_Elab_stxQuot_expand___closed__2 = _init_l_Lean_Elab_stxQuot_expand___closed__2();
lean_mark_persistent(l_Lean_Elab_stxQuot_expand___closed__2);
l_Lean_Elab_stxQuot_expand___closed__3 = _init_l_Lean_Elab_stxQuot_expand___closed__3();
lean_mark_persistent(l_Lean_Elab_stxQuot_expand___closed__3);
l_Lean_Elab_stxQuot_expand___closed__4 = _init_l_Lean_Elab_stxQuot_expand___closed__4();
lean_mark_persistent(l_Lean_Elab_stxQuot_expand___closed__4);
l_Lean_Elab_stxQuot_expand___closed__5 = _init_l_Lean_Elab_stxQuot_expand___closed__5();
lean_mark_persistent(l_Lean_Elab_stxQuot_expand___closed__5);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__1);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__2);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__3);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__4);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__5);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__6);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__7);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__8);
l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9 = _init_l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Quotation_8__toPreterm___main___closed__9);
l_Lean_Elab_oldParseStxQuot___closed__1 = _init_l_Lean_Elab_oldParseStxQuot___closed__1();
lean_mark_persistent(l_Lean_Elab_oldParseStxQuot___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
