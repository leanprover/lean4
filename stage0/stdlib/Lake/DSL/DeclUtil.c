// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: Init Lake.DSL.Config Lake.Util.Binder Lean.Parser.Command
#include <lean/lean.h>
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
static lean_object* l_Lake_DSL_mkConfigDecl___closed__1;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
static lean_object* l_Lake_DSL_declField___closed__8;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7;
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_simpleDeclSig;
static lean_object* l_Lake_DSL_declValWhere___closed__7;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
lean_object* l_Lean_Macro_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__13;
static lean_object* l_Lake_DSL_declValOptTyped___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__10;
static lean_object* l_Lake_DSL_simpleBinder___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_declValStruct;
static lean_object* l_Lake_DSL_expandDeclField___closed__4;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__32;
static lean_object* l_Lake_DSL_expandDeclField___closed__5;
static lean_object* l_Lake_DSL_declField___closed__14;
static lean_object* l_Lake_DSL_expandDeclField___closed__1;
static lean_object* l_Lake_DSL_declValDo___closed__8;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__1;
static lean_object* l_Lake_DSL_declValTyped___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__19;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__5;
static lean_object* l_Lake_DSL_structDeclSig___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__6;
static lean_object* l_Lake_DSL_declField___closed__13;
static lean_object* l_Lake_DSL_declValTyped___closed__6;
static lean_object* l_Lake_DSL_simpleBinder___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_declValTyped;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__12;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__5;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__13;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__1;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__29;
static lean_object* l_Lake_DSL_declValStruct___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_simpleBinder;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__27;
static lean_object* l_Lake_DSL_structDeclSig___closed__7;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lake_DSL_declField___closed__15;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__2;
static lean_object* l_Lake_DSL_declValDo___closed__3;
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__4;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__24;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__5;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__12;
static lean_object* l_Lake_DSL_expandAttrs___closed__1;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__31;
static lean_object* l_Lake_DSL_structVal___closed__7;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__26;
static lean_object* l_Lake_DSL_structVal___closed__16;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__5;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__27;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__11;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__4;
static lean_object* l_Lake_DSL_expandAttrs___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__12;
static lean_object* l_Lake_DSL_declField___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_bracketedSimpleBinder;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__35;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_declValWhere;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__22;
static lean_object* l_Lake_DSL_declValStruct___closed__1;
static lean_object* l_Lake_DSL_declValDo___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_declValOptTyped;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__13;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__15;
static lean_object* l_Lake_DSL_declValWhere___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__6;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__23;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__18;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__34;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__17;
static lean_object* l_Lake_DSL_simpleBinder___closed__2;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__2;
lean_object* l_Lean_quoteNameMk(lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
static lean_object* l_Lake_DSL_structVal___closed__21;
static lean_object* l_Lake_DSL_declValOptTyped___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_structDeclSig;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__4;
static lean_object* l_Lake_DSL_structVal___closed__17;
static lean_object* l_Lake_DSL_declField___closed__7;
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValTyped___closed__4;
static lean_object* l_Lake_DSL_declValWhere___closed__9;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__6;
static lean_object* l_Lake_DSL_simpleBinder___closed__3;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__8;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__24;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__3;
static lean_object* l_Lake_DSL_declValDo___closed__14;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValTyped___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__1;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValTyped___closed__10;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__10;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__23;
static lean_object* l_Lake_DSL_structDeclSig___closed__4;
static lean_object* l_Lake_DSL_structVal___closed__9;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__26;
static lean_object* l_Lake_DSL_declValDo___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__4;
static lean_object* l_Lake_DSL_declField___closed__16;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__15;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__16;
LEAN_EXPORT lean_object* l_Lake_DSL_structVal;
static lean_object* l_Lake_DSL_structDeclSig___closed__9;
static lean_object* l_Lake_DSL_structVal___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__8;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__22;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declValDo;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__28;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__2;
static lean_object* l_Lake_DSL_declValWhere___closed__8;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__21;
static lean_object* l_Lake_DSL_declField___closed__12;
static lean_object* l_Lake_DSL_declValOptTyped___closed__5;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__2;
static lean_object* l_Lake_DSL_structDeclSig___closed__1;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__18;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__14;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__4;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__33;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__30;
static lean_object* l_Lake_DSL_expandDeclField___closed__3;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_fixName(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__6;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__9;
static lean_object* l_Lake_DSL_structVal___closed__12;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDeclField___closed__2;
static lean_object* l_Lake_DSL_declField___closed__9;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__11;
static lean_object* l_Lake_DSL_structVal___closed__20;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__25;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__10;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declField;
static lean_object* l_Lake_DSL_structDeclSig___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValTyped___closed__11;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lake_DSL_expandDeclField___closed__6;
static lean_object* l_Lake_DSL_declValWhere___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1;
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__12;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__21;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__6;
static lean_object* l_Lake_DSL_declValStruct___closed__3;
static lean_object* l_Lake_DSL_declValWhere___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__7;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__5;
static lean_object* l_Lake_DSL_declValTyped___closed__5;
static lean_object* l_Lake_DSL_declValWhere___closed__2;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__1;
static lean_object* l_Lake_DSL_expandAttrs___closed__4;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__17;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_DSL_structVal___closed__14;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__10;
static lean_object* l_Lake_DSL_declField___closed__6;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_DSL_declValDo___closed__5;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__17;
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__2(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__8;
static lean_object* l_Lake_DSL_declValDo___closed__11;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1;
static lean_object* l_Lake_DSL_declValOptTyped___closed__3;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__25;
static lean_object* l_Lake_DSL_declField___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__11;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__20;
static lean_object* l_Lake_DSL_declField___closed__2;
static lean_object* l_Lake_DSL_structVal___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDeclField(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValOptTyped___closed__1;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__13;
static lean_object* l_Lake_DSL_declValDo___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__5;
static lean_object* l_Lake_DSL_structDeclSig___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___closed__18;
static lean_object* l_Lake_DSL_declField___closed__10;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__3;
static lean_object* l_Lake_DSL_structDeclSig___closed__5;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__5;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__4;
static lean_object* l_Lake_DSL_declValTyped___closed__7;
static lean_object* l_Lake_DSL_declValDo___closed__13;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__19;
static lean_object* l_Lake_DSL_declValTyped___closed__2;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__16;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__14;
static lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___closed__11;
static lean_object* l_Lake_DSL_declValTyped___closed__3;
static lean_object* l_Lake_DSL_declValTyped___closed__8;
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attributes", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_expandAttrs___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lake_DSL_expandAttrs___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_3);
x_5 = l_Lean_Syntax_isOfKind(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lake_DSL_expandAttrs___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = l_Lean_Syntax_TSepArray_getElems___rarg(x_9);
lean_dec(x_9);
return x_10;
}
}
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DSL", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declField", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declField___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declField___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declField___closed__10;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declField___closed__9;
x_3 = l_Lake_DSL_declField___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declField___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declField___closed__12;
x_3 = l_Lake_DSL_declField___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__3;
x_2 = l_Lake_DSL_declField___closed__4;
x_3 = l_Lake_DSL_declField___closed__16;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declField___closed__17;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structVal", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_structVal___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_structVal___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("manyIndent", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_structVal___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("group", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_structVal___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optional", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_structVal___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_structVal___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__10;
x_2 = l_Lake_DSL_structVal___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declField;
x_3 = l_Lake_DSL_structVal___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__8;
x_2 = l_Lake_DSL_structVal___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__6;
x_2 = l_Lake_DSL_structVal___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_structVal___closed__4;
x_3 = l_Lake_DSL_structVal___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_structVal___closed__18;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_structVal___closed__17;
x_3 = l_Lake_DSL_structVal___closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structVal___closed__1;
x_2 = l_Lake_DSL_structVal___closed__2;
x_3 = l_Lake_DSL_structVal___closed__20;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_structVal___closed__21;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValDo", 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declValDo___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ppSpace", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declValDo___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValDo___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("do", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_declValDo___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValDo___closed__7;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValDo___closed__5;
x_3 = l_Lake_DSL_declValDo___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("whereDecls", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_declValDo___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValDo___closed__11;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__10;
x_2 = l_Lake_DSL_declValDo___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValDo___closed__9;
x_3 = l_Lake_DSL_declValDo___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValDo___closed__1;
x_2 = l_Lake_DSL_declValDo___closed__2;
x_3 = l_Lake_DSL_declValDo___closed__14;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declValDo___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValStruct", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declValStruct___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValDo___closed__5;
x_3 = l_Lake_DSL_structVal;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValStruct___closed__3;
x_3 = l_Lake_DSL_declValDo___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValStruct___closed__1;
x_2 = l_Lake_DSL_declValStruct___closed__2;
x_3 = l_Lake_DSL_declValStruct___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declValStruct___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValWhere", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declValWhere___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" where ", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValWhere___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sepByIndentSemicolon", 20);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declValWhere___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declValWhere___closed__6;
x_2 = l_Lake_DSL_declField;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValWhere___closed__4;
x_3 = l_Lake_DSL_declValWhere___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValWhere___closed__8;
x_3 = l_Lake_DSL_declValDo___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValWhere___closed__1;
x_2 = l_Lake_DSL_declValWhere___closed__2;
x_3 = l_Lake_DSL_declValWhere___closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declValWhere___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValTyped", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declValTyped___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_declValTyped___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValTyped___closed__4;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_declValTyped___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValTyped___closed__8;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValTyped___closed__5;
x_3 = l_Lake_DSL_declValTyped___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValTyped___closed__1;
x_2 = l_Lake_DSL_declValTyped___closed__2;
x_3 = l_Lake_DSL_declValTyped___closed__10;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValTyped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declValTyped___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValOptTyped", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declValOptTyped___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__10;
x_2 = l_Lake_DSL_declValTyped___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declValOptTyped___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValOptTyped___closed__1;
x_2 = l_Lake_DSL_declValOptTyped___closed__2;
x_3 = l_Lake_DSL_declValOptTyped___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValOptTyped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_declValOptTyped___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpleDeclSig", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_simpleDeclSig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declField___closed__9;
x_3 = l_Lake_DSL_declValTyped___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_simpleDeclSig___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_simpleDeclSig___closed__1;
x_2 = l_Lake_DSL_simpleDeclSig___closed__2;
x_3 = l_Lake_DSL_simpleDeclSig___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_simpleDeclSig___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structDeclSig", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_structDeclSig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("orelse", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_structDeclSig___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structDeclSig___closed__4;
x_2 = l_Lake_DSL_declValOptTyped;
x_3 = l_Lake_DSL_declValStruct;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structDeclSig___closed__4;
x_2 = l_Lake_DSL_declValWhere;
x_3 = l_Lake_DSL_structDeclSig___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__10;
x_2 = l_Lake_DSL_structDeclSig___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_declField___closed__9;
x_3 = l_Lake_DSL_structDeclSig___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structDeclSig___closed__1;
x_2 = l_Lake_DSL_structDeclSig___closed__2;
x_3 = l_Lake_DSL_structDeclSig___closed__8;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_structDeclSig___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bracketedSimpleBinder", 21);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_bracketedSimpleBinder___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_bracketedSimpleBinder___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__4;
x_3 = l_Lake_DSL_declField___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_bracketedSimpleBinder___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__7;
x_3 = l_Lake_DSL_declField___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__10;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__5;
x_3 = l_Lake_DSL_bracketedSimpleBinder___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_bracketedSimpleBinder___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__6;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__10;
x_3 = l_Lake_DSL_bracketedSimpleBinder___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_bracketedSimpleBinder___closed__1;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__2;
x_3 = l_Lake_DSL_bracketedSimpleBinder___closed__13;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_bracketedSimpleBinder___closed__14;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpleBinder", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_simpleBinder___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structDeclSig___closed__4;
x_2 = l_Lake_DSL_declField___closed__9;
x_3 = l_Lake_DSL_bracketedSimpleBinder;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_simpleBinder___closed__1;
x_2 = l_Lake_DSL_simpleBinder___closed__2;
x_3 = l_Lake_DSL_simpleBinder___closed__3;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_simpleBinder___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscription", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = 0;
x_8 = l_Lean_SourceInfo_fromRef(x_6, x_7);
x_9 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_8);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
lean_inc(x_8);
x_12 = l_Lean_Syntax_node1(x_8, x_11, x_10);
x_13 = l_Lake_DSL_bracketedSimpleBinder___closed__3;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_8);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lake_DSL_bracketedSimpleBinder___closed__11;
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_8);
x_20 = l_Lean_Syntax_node1(x_8, x_19, x_12);
x_21 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5;
x_22 = l_Lean_Syntax_node5(x_8, x_21, x_14, x_1, x_16, x_20, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_8);
x_26 = l_Lean_Syntax_node1(x_8, x_25, x_24);
x_27 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5;
x_28 = l_Lean_Syntax_node5(x_8, x_27, x_14, x_1, x_16, x_26, x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 5);
lean_inc(x_4);
lean_dec(x_2);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
x_7 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_10 = l_Lean_Syntax_node1(x_6, x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lake_DSL_simpleBinder___closed__2;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_1);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_dec(x_2);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_16, x_17);
x_19 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_18);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_22 = l_Lean_Syntax_node1(x_18, x_21, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_13, x_24);
lean_dec(x_13);
x_26 = l_Lake_DSL_declField___closed__8;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lake_DSL_bracketedSimpleBinder___closed__2;
lean_inc(x_25);
x_29 = l_Lean_Syntax_isOfKind(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
lean_free_object(x_1);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
lean_dec(x_2);
x_31 = 0;
x_32 = l_Lean_SourceInfo_fromRef(x_30, x_31);
x_33 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_32);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_36 = l_Lean_Syntax_node1(x_32, x_35, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Syntax_getArg(x_25, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = l_Lean_Syntax_getArg(x_25, x_40);
lean_dec(x_25);
x_42 = l_Lean_Syntax_isNone(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_inc(x_41);
x_43 = l_Lean_Syntax_matchesNull(x_41, x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_39);
lean_free_object(x_1);
x_44 = lean_ctor_get(x_2, 5);
lean_inc(x_44);
lean_dec(x_2);
x_45 = 0;
x_46 = l_Lean_SourceInfo_fromRef(x_44, x_45);
x_47 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_46);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_50 = l_Lean_Syntax_node1(x_46, x_49, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Lean_Syntax_getArg(x_41, x_38);
lean_dec(x_41);
lean_ctor_set(x_1, 0, x_52);
x_53 = lean_box(0);
x_54 = l_Lake_DSL_expandOptSimpleBinder___lambda__1(x_39, x_53, x_1, x_2, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_free_object(x_1);
x_55 = lean_box(0);
x_56 = lean_box(0);
x_57 = l_Lake_DSL_expandOptSimpleBinder___lambda__1(x_39, x_56, x_55, x_2, x_3);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_free_object(x_1);
lean_dec(x_2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_25);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lake_DSL_simpleBinder___closed__2;
lean_inc(x_59);
x_61 = l_Lean_Syntax_isOfKind(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
x_62 = lean_ctor_get(x_2, 5);
lean_inc(x_62);
lean_dec(x_2);
x_63 = 0;
x_64 = l_Lean_SourceInfo_fromRef(x_62, x_63);
x_65 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_64);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_68 = l_Lean_Syntax_node1(x_64, x_67, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_59, x_70);
lean_dec(x_59);
x_72 = l_Lake_DSL_declField___closed__8;
lean_inc(x_71);
x_73 = l_Lean_Syntax_isOfKind(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lake_DSL_bracketedSimpleBinder___closed__2;
lean_inc(x_71);
x_75 = l_Lean_Syntax_isOfKind(x_71, x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_2, 5);
lean_inc(x_76);
lean_dec(x_2);
x_77 = 0;
x_78 = l_Lean_SourceInfo_fromRef(x_76, x_77);
x_79 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_78);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_82 = l_Lean_Syntax_node1(x_78, x_81, x_80);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = l_Lean_Syntax_getArg(x_71, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = l_Lean_Syntax_getArg(x_71, x_86);
lean_dec(x_71);
x_88 = l_Lean_Syntax_isNone(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_inc(x_87);
x_89 = l_Lean_Syntax_matchesNull(x_87, x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_87);
lean_dec(x_85);
x_90 = lean_ctor_get(x_2, 5);
lean_inc(x_90);
lean_dec(x_2);
x_91 = 0;
x_92 = l_Lean_SourceInfo_fromRef(x_90, x_91);
x_93 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
lean_inc(x_92);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
x_96 = l_Lean_Syntax_node1(x_92, x_95, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = l_Lean_Syntax_getArg(x_87, x_84);
lean_dec(x_87);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_box(0);
x_101 = l_Lake_DSL_expandOptSimpleBinder___lambda__1(x_85, x_100, x_99, x_2, x_3);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_87);
x_102 = lean_box(0);
x_103 = lean_box(0);
x_104 = l_Lake_DSL_expandOptSimpleBinder___lambda__1(x_85, x_103, x_102, x_2, x_3);
return x_104;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_2);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_71);
lean_ctor_set(x_105, 1, x_3);
return x_105;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DSL_expandOptSimpleBinder___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_fixName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = 0;
x_5 = l_Lean_mkIdentFrom(x_1, x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed field declaration", 28);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstField", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_expandDeclField___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstLVal", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_expandDeclField___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDeclField___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDeclField(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_DSL_declField___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_DSL_expandDeclField___closed__1;
x_7 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_6, x_2, x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
lean_dec(x_2);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_18 = l_Lake_DSL_expandAttrs___closed__1;
lean_inc(x_16);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lake_DSL_expandDeclField___closed__5;
lean_inc(x_16);
x_21 = l_Lean_Syntax_node2(x_16, x_20, x_9, x_19);
x_22 = 1;
x_23 = l_Lean_SourceInfo_fromRef(x_11, x_22);
x_24 = l_Lake_DSL_expandDeclField___closed__6;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lake_DSL_expandDeclField___closed__3;
x_27 = l_Lean_Syntax_node3(x_16, x_26, x_21, x_25, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
lean_inc(x_4);
x_11 = l_Lake_DSL_expandDeclField(x_8, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_10, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_DSL_structVal___closed__8;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Syntax_matchesNull(x_8, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInst", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__3;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstFieldAbbrev", 21);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDeclField___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__8;
x_2 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optEllipsis", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("abbrev", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__21;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandAttrs___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Termination", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("suffix", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__27;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__28;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandAttrs___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quotedName", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__31;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_box(0);
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_9);
x_15 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3(x_13, x_14, x_1, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_9, 5);
lean_inc(x_19);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_19, x_20);
x_22 = lean_ctor_get(x_9, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = l_Lake_DSL_structVal___closed__3;
lean_inc(x_21);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_27 = l_Lake_DSL_expandAttrs___closed__1;
lean_inc(x_21);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__5;
x_30 = l_Lean_addMacroScope(x_23, x_29, x_22);
x_31 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__4;
lean_inc(x_21);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_11);
x_33 = l_Lake_DSL_expandDeclField___closed__5;
lean_inc(x_28);
lean_inc(x_21);
x_34 = l_Lean_Syntax_node2(x_21, x_33, x_32, x_28);
x_35 = l_Lake_DSL_expandDeclField___closed__6;
lean_inc(x_21);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Syntax_getId(x_2);
lean_inc(x_37);
x_38 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_11, x_37);
x_39 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__6;
lean_inc(x_21);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_get_size(x_16);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__10;
x_44 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4(x_43, x_42, x_14, x_16);
x_45 = l_Lean_Syntax_SepArray_ofElems(x_39, x_44);
lean_dec(x_44);
x_46 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__12;
lean_inc(x_28);
lean_inc(x_21);
x_47 = l_Lean_Syntax_node1(x_21, x_46, x_28);
x_48 = l_Lake_DSL_structVal___closed__18;
lean_inc(x_21);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_21);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__17;
lean_inc(x_21);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Syntax_SepArray_ofElems(x_39, x_3);
x_53 = l_Array_append___rarg(x_27, x_52);
lean_inc(x_21);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_21);
lean_ctor_set(x_54, 1, x_26);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__18;
lean_inc(x_21);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_21);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_21);
x_58 = l_Lean_Syntax_node3(x_21, x_57, x_51, x_54, x_56);
lean_inc(x_21);
x_59 = l_Lean_Syntax_node1(x_21, x_26, x_58);
x_60 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
lean_inc(x_21);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_21);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lake_DSL_fixName(x_2, x_4);
x_63 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__24;
x_64 = lean_array_push(x_63, x_62);
x_65 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__23;
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_box(2);
x_68 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__22;
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_66);
x_70 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_21);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_21);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lake_DSL_declValTyped___closed__4;
lean_inc(x_21);
x_73 = l_Lean_Syntax_node2(x_21, x_72, x_71, x_5);
lean_inc(x_21);
x_74 = l_Lean_Syntax_node1(x_21, x_26, x_73);
x_75 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__26;
lean_inc(x_28);
lean_inc(x_21);
x_76 = l_Lean_Syntax_node2(x_21, x_75, x_28, x_74);
x_77 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__29;
lean_inc_n(x_28, 2);
lean_inc(x_21);
x_78 = l_Lean_Syntax_node2(x_21, x_77, x_28, x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_116; 
x_116 = l_Lean_quoteNameMk(x_37);
x_79 = x_116;
goto block_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_37);
x_117 = lean_ctor_get(x_38, 0);
lean_inc(x_117);
lean_dec(x_38);
x_118 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__33;
x_119 = l_String_intercalate(x_118, x_117);
x_120 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__34;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_Lean_Syntax_mkNameLit(x_121, x_67);
x_123 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__35;
x_124 = lean_array_push(x_123, x_122);
x_125 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__32;
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_67);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_124);
x_79 = x_126;
goto block_115;
}
block_115:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = l_Lake_DSL_expandDeclField___closed__3;
lean_inc(x_36);
lean_inc(x_21);
x_81 = l_Lean_Syntax_node3(x_21, x_80, x_34, x_36, x_79);
x_82 = l_Array_mkArray2___rarg(x_81, x_40);
x_83 = l_Array_append___rarg(x_82, x_45);
lean_inc(x_21);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_21);
lean_ctor_set(x_84, 1, x_26);
lean_ctor_set(x_84, 2, x_83);
x_85 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__2;
lean_inc_n(x_28, 2);
lean_inc(x_21);
x_86 = l_Lean_Syntax_node6(x_21, x_85, x_25, x_28, x_84, x_47, x_28, x_49);
if (lean_obj_tag(x_6) == 0)
{
x_87 = x_27;
goto block_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_6, 0);
lean_inc(x_113);
lean_dec(x_6);
x_114 = l_Array_mkArray1___rarg(x_113);
x_87 = x_114;
goto block_112;
}
block_112:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Array_append___rarg(x_27, x_87);
lean_inc(x_21);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_21);
lean_ctor_set(x_89, 1, x_26);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__16;
lean_inc_n(x_28, 3);
lean_inc(x_21);
x_91 = l_Lean_Syntax_node6(x_21, x_90, x_89, x_59, x_28, x_28, x_28, x_28);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__30;
lean_inc(x_21);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_21);
lean_ctor_set(x_93, 1, x_26);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_21);
x_95 = l_Lean_Syntax_node4(x_21, x_94, x_36, x_86, x_78, x_93);
x_96 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_21);
x_97 = l_Lean_Syntax_node4(x_21, x_96, x_61, x_69, x_76, x_95);
x_98 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_99 = l_Lean_Syntax_node2(x_21, x_98, x_91, x_97);
if (lean_is_scalar(x_18)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_18;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_17);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_8, 0);
lean_inc(x_101);
lean_dec(x_8);
x_102 = l_Array_mkArray1___rarg(x_101);
x_103 = l_Array_append___rarg(x_27, x_102);
lean_inc(x_21);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_21);
lean_ctor_set(x_104, 1, x_26);
lean_ctor_set(x_104, 2, x_103);
x_105 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_21);
x_106 = l_Lean_Syntax_node4(x_21, x_105, x_36, x_86, x_78, x_104);
x_107 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_21);
x_108 = l_Lean_Syntax_node4(x_21, x_107, x_61, x_69, x_76, x_106);
x_109 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_110 = l_Lean_Syntax_node2(x_21, x_109, x_91, x_108);
if (lean_is_scalar(x_18)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_18;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_17);
return x_111;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_15);
if (x_127 == 0)
{
return x_15;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_15, 0);
x_129 = lean_ctor_get(x_15, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_15);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed configuration syntax", 31);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eval", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_declValTyped___closed__6;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#eval", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.eprintln", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__7;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eprintln", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__9;
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__12;
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termS!_", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("s!", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStrKind", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("interpolatedStrLitKind", 22);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\" warning: {", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dirConst", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__24;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("__dir__", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}: `:=` syntax for configurations has been deprecated\"", 54);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_22 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_21, x_15, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_3, x_23);
x_25 = l_Lean_Syntax_matchesNull(x_24, x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_27 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_26, x_15, x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_28 = lean_ctor_get(x_15, 5);
lean_inc(x_28);
x_29 = l_Lean_replaceRef(x_4, x_28);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_31);
lean_dec(x_15);
x_32 = 0;
x_33 = l_Lean_SourceInfo_fromRef(x_29, x_32);
x_34 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__4;
lean_inc(x_33);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__11;
x_37 = l_Lean_addMacroScope(x_30, x_36, x_31);
x_38 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__8;
x_39 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__15;
lean_inc(x_33);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__18;
lean_inc(x_33);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__23;
lean_inc(x_33);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__22;
lean_inc(x_33);
x_46 = l_Lean_Syntax_node1(x_33, x_45, x_44);
x_47 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__26;
lean_inc(x_33);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__25;
lean_inc(x_33);
x_50 = l_Lean_Syntax_node1(x_33, x_49, x_48);
x_51 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__27;
lean_inc(x_33);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_33);
x_53 = l_Lean_Syntax_node1(x_33, x_45, x_52);
x_54 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__20;
lean_inc(x_33);
x_55 = l_Lean_Syntax_node3(x_33, x_54, x_46, x_50, x_53);
x_56 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__17;
lean_inc(x_33);
x_57 = l_Lean_Syntax_node2(x_33, x_56, x_42, x_55);
x_58 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_33);
x_59 = l_Lean_Syntax_node1(x_33, x_58, x_57);
x_60 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__6;
lean_inc(x_33);
x_61 = l_Lean_Syntax_node2(x_33, x_60, x_40, x_59);
x_62 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__3;
x_63 = l_Lean_Syntax_node2(x_33, x_62, x_35, x_61);
x_64 = l_Lean_SourceInfo_fromRef(x_28, x_32);
x_65 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__17;
lean_inc(x_64);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__6;
x_68 = l_Lean_Syntax_SepArray_ofElems(x_67, x_5);
x_69 = l_Lake_DSL_expandAttrs___closed__1;
x_70 = l_Array_append___rarg(x_69, x_68);
lean_inc(x_64);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_58);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__18;
lean_inc(x_64);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_64);
x_75 = l_Lean_Syntax_node3(x_64, x_74, x_66, x_71, x_73);
lean_inc(x_64);
x_76 = l_Lean_Syntax_node1(x_64, x_58, x_75);
lean_inc(x_64);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_58);
lean_ctor_set(x_77, 2, x_69);
x_78 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
lean_inc(x_64);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lake_DSL_fixName(x_6, x_7);
x_81 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__24;
x_82 = lean_array_push(x_81, x_80);
x_83 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__23;
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_box(2);
x_86 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__22;
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_84);
x_88 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_64);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_64);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lake_DSL_declValTyped___closed__4;
lean_inc(x_64);
x_91 = l_Lean_Syntax_node2(x_64, x_90, x_89, x_8);
lean_inc(x_64);
x_92 = l_Lean_Syntax_node1(x_64, x_58, x_91);
x_93 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__26;
lean_inc(x_77);
lean_inc(x_64);
x_94 = l_Lean_Syntax_node2(x_64, x_93, x_77, x_92);
x_95 = l_Lake_DSL_expandDeclField___closed__6;
lean_inc(x_64);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_64);
lean_ctor_set(x_96, 1, x_95);
if (lean_obj_tag(x_12) == 0)
{
x_97 = x_69;
goto block_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_12, 0);
lean_inc(x_125);
lean_dec(x_12);
x_126 = l_Array_mkArray1___rarg(x_125);
x_97 = x_126;
goto block_124;
}
block_124:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = l_Array_append___rarg(x_69, x_97);
lean_inc(x_64);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_64);
lean_ctor_set(x_99, 1, x_58);
lean_ctor_set(x_99, 2, x_98);
x_100 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__16;
lean_inc_n(x_77, 4);
lean_inc(x_64);
x_101 = l_Lean_Syntax_node6(x_64, x_100, x_99, x_76, x_77, x_77, x_77, x_77);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__30;
lean_inc(x_64);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_64);
lean_ctor_set(x_103, 1, x_58);
lean_ctor_set(x_103, 2, x_102);
lean_inc(x_77);
lean_inc(x_64);
x_104 = l_Lean_Syntax_node2(x_64, x_9, x_103, x_77);
lean_inc(x_64);
x_105 = l_Lean_Syntax_node4(x_64, x_10, x_96, x_11, x_104, x_77);
x_106 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_64);
x_107 = l_Lean_Syntax_node4(x_64, x_106, x_79, x_87, x_94, x_105);
x_108 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
lean_inc(x_64);
x_109 = l_Lean_Syntax_node2(x_64, x_108, x_101, x_107);
x_110 = l_Lean_Syntax_node2(x_64, x_58, x_63, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_16);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_112 = lean_ctor_get(x_14, 0);
lean_inc(x_112);
lean_dec(x_14);
x_113 = l_Array_mkArray1___rarg(x_112);
x_114 = l_Array_append___rarg(x_69, x_113);
lean_inc(x_64);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_64);
lean_ctor_set(x_115, 1, x_58);
lean_ctor_set(x_115, 2, x_114);
lean_inc(x_77);
lean_inc(x_64);
x_116 = l_Lean_Syntax_node2(x_64, x_9, x_115, x_77);
lean_inc(x_64);
x_117 = l_Lean_Syntax_node4(x_64, x_10, x_96, x_11, x_116, x_77);
x_118 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_64);
x_119 = l_Lean_Syntax_node4(x_64, x_118, x_79, x_87, x_94, x_117);
x_120 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
lean_inc(x_64);
x_121 = l_Lean_Syntax_node2(x_64, x_120, x_101, x_119);
x_122 = l_Lean_Syntax_node2(x_64, x_58, x_63, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_16);
return x_123;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_16, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
x_20 = l_Lean_Syntax_getArg(x_13, x_12);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_13, x_21);
x_23 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__29;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_26 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_25, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Syntax_getArg(x_22, x_18);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_inc(x_27);
x_29 = l_Lean_Syntax_matchesNull(x_27, x_12);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_31 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_30, x_10, x_11);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Syntax_getArg(x_27, x_18);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = l_Lake_DSL_mkConfigDecl___lambda__4(x_22, x_2, x_13, x_19, x_3, x_4, x_5, x_6, x_23, x_14, x_20, x_7, x_34, x_33, x_10, x_11);
lean_dec(x_3);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_22);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = l_Lake_DSL_mkConfigDecl___lambda__4(x_22, x_2, x_13, x_19, x_3, x_4, x_5, x_6, x_23, x_14, x_20, x_7, x_37, x_36, x_10, x_11);
lean_dec(x_3);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_22);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = l_Lean_Syntax_getArgs(x_1);
x_13 = l_Lean_Syntax_TSepArray_getElems___rarg(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
x_17 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3(x_15, x_16, x_13, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = lean_ctor_get(x_9, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = l_Lake_DSL_structVal___closed__3;
lean_inc(x_23);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_29 = l_Lake_DSL_expandAttrs___closed__1;
lean_inc(x_23);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__5;
x_32 = l_Lean_addMacroScope(x_25, x_31, x_24);
x_33 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__4;
lean_inc(x_23);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_11);
x_35 = l_Lake_DSL_expandDeclField___closed__5;
lean_inc(x_30);
lean_inc(x_23);
x_36 = l_Lean_Syntax_node2(x_23, x_35, x_34, x_30);
x_37 = l_Lake_DSL_expandDeclField___closed__6;
lean_inc(x_23);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_getId(x_2);
lean_inc(x_39);
x_40 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_11, x_39);
x_41 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__6;
lean_inc(x_23);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_get_size(x_18);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__10;
x_46 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5(x_45, x_44, x_16, x_18);
x_47 = l_Lean_Syntax_SepArray_ofElems(x_41, x_46);
lean_dec(x_46);
x_48 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__12;
lean_inc(x_30);
lean_inc(x_23);
x_49 = l_Lean_Syntax_node1(x_23, x_48, x_30);
x_50 = l_Lake_DSL_structVal___closed__18;
lean_inc(x_23);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__17;
lean_inc(x_23);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Syntax_SepArray_ofElems(x_41, x_3);
x_55 = l_Array_append___rarg(x_29, x_54);
lean_inc(x_23);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_23);
lean_ctor_set(x_56, 1, x_28);
lean_ctor_set(x_56, 2, x_55);
x_57 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__18;
lean_inc(x_23);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_23);
x_60 = l_Lean_Syntax_node3(x_23, x_59, x_53, x_56, x_58);
lean_inc(x_23);
x_61 = l_Lean_Syntax_node1(x_23, x_28, x_60);
x_62 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
lean_inc(x_23);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_23);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lake_DSL_fixName(x_2, x_4);
x_65 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__24;
x_66 = lean_array_push(x_65, x_64);
x_67 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__23;
x_68 = lean_array_push(x_66, x_67);
x_69 = lean_box(2);
x_70 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__22;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_68);
x_72 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_23);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lake_DSL_declValTyped___closed__4;
lean_inc(x_23);
x_75 = l_Lean_Syntax_node2(x_23, x_74, x_73, x_5);
lean_inc(x_23);
x_76 = l_Lean_Syntax_node1(x_23, x_28, x_75);
x_77 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__26;
lean_inc(x_30);
lean_inc(x_23);
x_78 = l_Lean_Syntax_node2(x_23, x_77, x_30, x_76);
x_79 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__29;
lean_inc_n(x_30, 2);
lean_inc(x_23);
x_80 = l_Lean_Syntax_node2(x_23, x_79, x_30, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_118; 
x_118 = l_Lean_quoteNameMk(x_39);
x_81 = x_118;
goto block_117;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_39);
x_119 = lean_ctor_get(x_40, 0);
lean_inc(x_119);
lean_dec(x_40);
x_120 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__33;
x_121 = l_String_intercalate(x_120, x_119);
x_122 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__34;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l_Lean_Syntax_mkNameLit(x_123, x_69);
x_125 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__35;
x_126 = lean_array_push(x_125, x_124);
x_127 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__32;
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_69);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_126);
x_81 = x_128;
goto block_117;
}
block_117:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = l_Lake_DSL_expandDeclField___closed__3;
lean_inc(x_38);
lean_inc(x_23);
x_83 = l_Lean_Syntax_node3(x_23, x_82, x_36, x_38, x_81);
x_84 = l_Array_mkArray2___rarg(x_83, x_42);
x_85 = l_Array_append___rarg(x_84, x_47);
lean_inc(x_23);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_23);
lean_ctor_set(x_86, 1, x_28);
lean_ctor_set(x_86, 2, x_85);
x_87 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__2;
lean_inc_n(x_30, 2);
lean_inc(x_23);
x_88 = l_Lean_Syntax_node6(x_23, x_87, x_27, x_30, x_86, x_49, x_30, x_51);
if (lean_obj_tag(x_6) == 0)
{
x_89 = x_29;
goto block_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_6, 0);
lean_inc(x_115);
lean_dec(x_6);
x_116 = l_Array_mkArray1___rarg(x_115);
x_89 = x_116;
goto block_114;
}
block_114:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = l_Array_append___rarg(x_29, x_89);
lean_inc(x_23);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_23);
lean_ctor_set(x_91, 1, x_28);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__16;
lean_inc_n(x_30, 3);
lean_inc(x_23);
x_93 = l_Lean_Syntax_node6(x_23, x_92, x_91, x_61, x_30, x_30, x_30, x_30);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__30;
lean_inc(x_23);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_23);
lean_ctor_set(x_95, 1, x_28);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_23);
x_97 = l_Lean_Syntax_node4(x_23, x_96, x_38, x_88, x_80, x_95);
x_98 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_23);
x_99 = l_Lean_Syntax_node4(x_23, x_98, x_63, x_71, x_78, x_97);
x_100 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_101 = l_Lean_Syntax_node2(x_23, x_100, x_93, x_99);
if (lean_is_scalar(x_20)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_20;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_19);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_8, 0);
lean_inc(x_103);
lean_dec(x_8);
x_104 = l_Array_mkArray1___rarg(x_103);
x_105 = l_Array_append___rarg(x_29, x_104);
lean_inc(x_23);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_23);
lean_ctor_set(x_106, 1, x_28);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_23);
x_108 = l_Lean_Syntax_node4(x_23, x_107, x_38, x_88, x_80, x_106);
x_109 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_23);
x_110 = l_Lean_Syntax_node4(x_23, x_109, x_63, x_71, x_78, x_108);
x_111 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_112 = l_Lean_Syntax_node2(x_23, x_111, x_93, x_110);
if (lean_is_scalar(x_20)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_20;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_19);
return x_113;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_17);
if (x_129 == 0)
{
return x_17;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_17, 0);
x_131 = lean_ctor_get(x_17, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_17);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
static lean_object* _init_l_Lake_DSL_mkConfigDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_DSL_mkConfigDecl___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_DSL_structDeclSig___closed__2;
lean_inc(x_5);
x_9 = l_Lean_Syntax_isOfKind(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_11 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_10, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_5, x_12);
x_14 = l_Lake_DSL_declField___closed__8;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_16, x_6, x_7);
lean_dec(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_5, x_18);
lean_inc(x_19);
x_20 = l_Lean_Syntax_matchesNull(x_19, x_12);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc(x_19);
x_21 = l_Lean_Syntax_matchesNull(x_19, x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_23 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_22, x_6, x_7);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Syntax_getArg(x_19, x_12);
lean_dec(x_19);
x_25 = l_Lake_DSL_declValWhere___closed__2;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lake_DSL_declValOptTyped___closed__2;
lean_inc(x_24);
x_28 = l_Lean_Syntax_isOfKind(x_24, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lake_DSL_declValStruct___closed__2;
lean_inc(x_24);
x_30 = l_Lean_Syntax_isOfKind(x_24, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_32 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_31, x_6, x_7);
lean_dec(x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Syntax_getArg(x_24, x_12);
x_34 = l_Lake_DSL_structVal___closed__2;
lean_inc(x_33);
x_35 = l_Lean_Syntax_isOfKind(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_37 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_36, x_6, x_7);
lean_dec(x_5);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Syntax_getArg(x_33, x_18);
lean_dec(x_33);
x_39 = l_Lean_Syntax_getArgs(x_38);
lean_dec(x_38);
x_40 = l_Lake_DSL_mkConfigDecl___closed__1;
x_41 = l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1(x_39, x_40);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_43 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_42, x_6, x_7);
lean_dec(x_5);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = l_Lean_Syntax_getArg(x_24, x_18);
lean_dec(x_24);
x_47 = l_Lean_Syntax_isNone(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_inc(x_46);
x_48 = l_Lean_Syntax_matchesNull(x_46, x_18);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_50 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_49, x_6, x_7);
lean_dec(x_5);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l_Lean_Syntax_getArg(x_46, x_12);
lean_dec(x_46);
x_52 = l_Lake_DSL_declValDo___closed__11;
lean_inc(x_51);
x_53 = l_Lean_Syntax_isOfKind(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_55 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_54, x_6, x_7);
lean_dec(x_5);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_ctor_set(x_41, 0, x_51);
x_56 = lean_box(0);
x_57 = l_Lake_DSL_mkConfigDecl___lambda__3(x_45, x_13, x_3, x_1, x_4, x_2, x_56, x_41, x_6, x_7);
lean_dec(x_3);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_5);
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = l_Lake_DSL_mkConfigDecl___lambda__3(x_45, x_13, x_3, x_1, x_4, x_2, x_59, x_58, x_6, x_7);
lean_dec(x_3);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
lean_dec(x_41);
x_62 = l_Lean_Syntax_getArg(x_24, x_18);
lean_dec(x_24);
x_63 = l_Lean_Syntax_isNone(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_inc(x_62);
x_64 = l_Lean_Syntax_matchesNull(x_62, x_18);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_66 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_65, x_6, x_7);
lean_dec(x_5);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_Syntax_getArg(x_62, x_12);
lean_dec(x_62);
x_68 = l_Lake_DSL_declValDo___closed__11;
lean_inc(x_67);
x_69 = l_Lean_Syntax_isOfKind(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_71 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_70, x_6, x_7);
lean_dec(x_5);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_73 = lean_box(0);
x_74 = l_Lake_DSL_mkConfigDecl___lambda__3(x_61, x_13, x_3, x_1, x_4, x_2, x_73, x_72, x_6, x_7);
lean_dec(x_3);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
lean_dec(x_5);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = l_Lake_DSL_mkConfigDecl___lambda__3(x_61, x_13, x_3, x_1, x_4, x_2, x_76, x_75, x_6, x_7);
lean_dec(x_3);
return x_77;
}
}
}
}
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Syntax_getArg(x_24, x_12);
x_79 = l_Lean_Syntax_isNone(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_inc(x_78);
x_80 = l_Lean_Syntax_matchesNull(x_78, x_18);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_82 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_81, x_6, x_7);
lean_dec(x_5);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = l_Lean_Syntax_getArg(x_78, x_12);
lean_dec(x_78);
x_84 = l_Lake_DSL_declValTyped___closed__4;
lean_inc(x_83);
x_85 = l_Lean_Syntax_isOfKind(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_87 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_86, x_6, x_7);
lean_dec(x_5);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Lean_Syntax_getArg(x_83, x_18);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_box(0);
x_91 = l_Lake_DSL_mkConfigDecl___lambda__5(x_24, x_5, x_3, x_13, x_1, x_4, x_2, x_90, x_89, x_6, x_7);
lean_dec(x_5);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_78);
x_92 = lean_box(0);
x_93 = lean_box(0);
x_94 = l_Lake_DSL_mkConfigDecl___lambda__5(x_24, x_5, x_3, x_13, x_1, x_4, x_2, x_93, x_92, x_6, x_7);
lean_dec(x_5);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = l_Lean_Syntax_getArg(x_24, x_18);
x_96 = lean_unsigned_to_nat(2u);
x_97 = l_Lean_Syntax_getArg(x_24, x_96);
lean_dec(x_24);
x_98 = l_Lean_Syntax_isNone(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
lean_inc(x_97);
x_99 = l_Lean_Syntax_matchesNull(x_97, x_18);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_101 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_100, x_6, x_7);
lean_dec(x_5);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_Syntax_getArg(x_97, x_12);
lean_dec(x_97);
x_103 = l_Lake_DSL_declValDo___closed__11;
lean_inc(x_102);
x_104 = l_Lean_Syntax_isOfKind(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_95);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = l_Lake_DSL_mkConfigDecl___lambda__4___closed__1;
x_106 = l_Lean_Macro_throwErrorAt___rarg(x_5, x_105, x_6, x_7);
lean_dec(x_5);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_5);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_108 = lean_box(0);
x_109 = l_Lake_DSL_mkConfigDecl___lambda__6(x_95, x_13, x_3, x_1, x_4, x_2, x_108, x_107, x_6, x_7);
lean_dec(x_3);
lean_dec(x_95);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_97);
lean_dec(x_5);
x_110 = lean_box(0);
x_111 = lean_box(0);
x_112 = l_Lake_DSL_mkConfigDecl___lambda__6(x_95, x_13, x_3, x_1, x_4, x_2, x_111, x_110, x_6, x_7);
lean_dec(x_3);
lean_dec(x_95);
return x_112;
}
}
}
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_19);
lean_dec(x_5);
x_113 = lean_ctor_get(x_6, 5);
lean_inc(x_113);
x_114 = 0;
x_115 = l_Lean_SourceInfo_fromRef(x_113, x_114);
x_116 = lean_ctor_get(x_6, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_6, 1);
lean_inc(x_117);
lean_dec(x_6);
x_118 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__17;
lean_inc(x_115);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__6;
x_121 = l_Lean_Syntax_SepArray_ofElems(x_120, x_3);
lean_dec(x_3);
x_122 = l_Lake_DSL_expandAttrs___closed__1;
x_123 = l_Array_append___rarg(x_122, x_121);
x_124 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_115);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_123);
x_126 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__18;
lean_inc(x_115);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_115);
x_129 = l_Lean_Syntax_node3(x_115, x_128, x_119, x_125, x_127);
lean_inc(x_115);
x_130 = l_Lean_Syntax_node1(x_115, x_124, x_129);
lean_inc(x_115);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_115);
lean_ctor_set(x_131, 1, x_124);
lean_ctor_set(x_131, 2, x_122);
x_132 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__19;
lean_inc(x_115);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_115);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_13);
x_134 = l_Lake_DSL_fixName(x_13, x_1);
x_135 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__24;
x_136 = lean_array_push(x_135, x_134);
x_137 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__23;
x_138 = lean_array_push(x_136, x_137);
x_139 = lean_box(2);
x_140 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__22;
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_138);
x_142 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_115);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lake_DSL_declValTyped___closed__4;
lean_inc(x_115);
x_145 = l_Lean_Syntax_node2(x_115, x_144, x_143, x_4);
lean_inc(x_115);
x_146 = l_Lean_Syntax_node1(x_115, x_124, x_145);
x_147 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__26;
lean_inc(x_131);
lean_inc(x_115);
x_148 = l_Lean_Syntax_node2(x_115, x_147, x_131, x_146);
x_149 = l_Lake_DSL_expandDeclField___closed__6;
lean_inc(x_115);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_115);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lake_DSL_structVal___closed__3;
lean_inc(x_115);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_115);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__5;
x_154 = l_Lean_addMacroScope(x_117, x_153, x_116);
x_155 = lean_box(0);
x_156 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__4;
lean_inc(x_115);
x_157 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_157, 0, x_115);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_154);
lean_ctor_set(x_157, 3, x_155);
x_158 = l_Lake_DSL_expandDeclField___closed__5;
lean_inc(x_131);
lean_inc(x_115);
x_159 = l_Lean_Syntax_node2(x_115, x_158, x_157, x_131);
x_160 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
lean_inc(x_160);
x_161 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_155, x_160);
x_162 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__12;
lean_inc(x_131);
lean_inc(x_115);
x_163 = l_Lean_Syntax_node1(x_115, x_162, x_131);
x_164 = l_Lake_DSL_structVal___closed__18;
lean_inc(x_115);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_115);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__29;
lean_inc_n(x_131, 2);
lean_inc(x_115);
x_167 = l_Lean_Syntax_node2(x_115, x_166, x_131, x_131);
if (lean_obj_tag(x_2) == 0)
{
x_168 = x_122;
goto block_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_2, 0);
lean_inc(x_209);
lean_dec(x_2);
x_210 = l_Array_mkArray1___rarg(x_209);
x_168 = x_210;
goto block_208;
}
block_208:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = l_Array_append___rarg(x_122, x_168);
lean_inc(x_115);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_115);
lean_ctor_set(x_170, 1, x_124);
lean_ctor_set(x_170, 2, x_169);
x_171 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__16;
lean_inc_n(x_131, 4);
lean_inc(x_115);
x_172 = l_Lean_Syntax_node6(x_115, x_171, x_170, x_130, x_131, x_131, x_131, x_131);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_173 = l_Lean_quoteNameMk(x_160);
x_174 = l_Lake_DSL_expandDeclField___closed__3;
lean_inc(x_150);
lean_inc(x_115);
x_175 = l_Lean_Syntax_node3(x_115, x_174, x_159, x_150, x_173);
lean_inc(x_115);
x_176 = l_Lean_Syntax_node1(x_115, x_124, x_175);
x_177 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__2;
lean_inc_n(x_131, 2);
lean_inc(x_115);
x_178 = l_Lean_Syntax_node6(x_115, x_177, x_152, x_131, x_176, x_163, x_131, x_165);
x_179 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_115);
x_180 = l_Lean_Syntax_node4(x_115, x_179, x_150, x_178, x_167, x_131);
x_181 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_115);
x_182 = l_Lean_Syntax_node4(x_115, x_181, x_133, x_141, x_148, x_180);
x_183 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_184 = l_Lean_Syntax_node2(x_115, x_183, x_172, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_7);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_160);
x_186 = lean_ctor_get(x_161, 0);
lean_inc(x_186);
lean_dec(x_161);
x_187 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__33;
x_188 = l_String_intercalate(x_187, x_186);
x_189 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__34;
x_190 = lean_string_append(x_189, x_188);
lean_dec(x_188);
x_191 = l_Lean_Syntax_mkNameLit(x_190, x_139);
x_192 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__35;
x_193 = lean_array_push(x_192, x_191);
x_194 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__32;
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_139);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_193);
x_196 = l_Lake_DSL_expandDeclField___closed__3;
lean_inc(x_150);
lean_inc(x_115);
x_197 = l_Lean_Syntax_node3(x_115, x_196, x_159, x_150, x_195);
lean_inc(x_115);
x_198 = l_Lean_Syntax_node1(x_115, x_124, x_197);
x_199 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__2;
lean_inc_n(x_131, 2);
lean_inc(x_115);
x_200 = l_Lean_Syntax_node6(x_115, x_199, x_152, x_131, x_198, x_163, x_131, x_165);
x_201 = l_Lake_DSL_declValTyped___closed__8;
lean_inc(x_115);
x_202 = l_Lean_Syntax_node4(x_115, x_201, x_150, x_200, x_167, x_131);
x_203 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__20;
lean_inc(x_115);
x_204 = l_Lean_Syntax_node4(x_115, x_203, x_133, x_141, x_148, x_202);
x_205 = l_Lake_DSL_mkConfigDecl___lambda__3___closed__14;
x_206 = l_Lean_Syntax_node2(x_115, x_205, x_172, x_204);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_7);
return x_207;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lake_DSL_mkConfigDecl___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lake_DSL_mkConfigDecl___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__3(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_DSL_mkConfigDecl___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_DSL_mkConfigDecl___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_DSL_mkConfigDecl___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lake_DSL_mkConfigDecl___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_mkConfigDecl___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDecl___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_DSL_mkConfigDecl___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Binder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_expandAttrs___closed__1 = _init_l_Lake_DSL_expandAttrs___closed__1();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__1);
l_Lake_DSL_expandAttrs___closed__2 = _init_l_Lake_DSL_expandAttrs___closed__2();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__2);
l_Lake_DSL_expandAttrs___closed__3 = _init_l_Lake_DSL_expandAttrs___closed__3();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__3);
l_Lake_DSL_expandAttrs___closed__4 = _init_l_Lake_DSL_expandAttrs___closed__4();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__4);
l_Lake_DSL_expandAttrs___closed__5 = _init_l_Lake_DSL_expandAttrs___closed__5();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__5);
l_Lake_DSL_expandAttrs___closed__6 = _init_l_Lake_DSL_expandAttrs___closed__6();
lean_mark_persistent(l_Lake_DSL_expandAttrs___closed__6);
l_Lake_DSL_declField___closed__1 = _init_l_Lake_DSL_declField___closed__1();
lean_mark_persistent(l_Lake_DSL_declField___closed__1);
l_Lake_DSL_declField___closed__2 = _init_l_Lake_DSL_declField___closed__2();
lean_mark_persistent(l_Lake_DSL_declField___closed__2);
l_Lake_DSL_declField___closed__3 = _init_l_Lake_DSL_declField___closed__3();
lean_mark_persistent(l_Lake_DSL_declField___closed__3);
l_Lake_DSL_declField___closed__4 = _init_l_Lake_DSL_declField___closed__4();
lean_mark_persistent(l_Lake_DSL_declField___closed__4);
l_Lake_DSL_declField___closed__5 = _init_l_Lake_DSL_declField___closed__5();
lean_mark_persistent(l_Lake_DSL_declField___closed__5);
l_Lake_DSL_declField___closed__6 = _init_l_Lake_DSL_declField___closed__6();
lean_mark_persistent(l_Lake_DSL_declField___closed__6);
l_Lake_DSL_declField___closed__7 = _init_l_Lake_DSL_declField___closed__7();
lean_mark_persistent(l_Lake_DSL_declField___closed__7);
l_Lake_DSL_declField___closed__8 = _init_l_Lake_DSL_declField___closed__8();
lean_mark_persistent(l_Lake_DSL_declField___closed__8);
l_Lake_DSL_declField___closed__9 = _init_l_Lake_DSL_declField___closed__9();
lean_mark_persistent(l_Lake_DSL_declField___closed__9);
l_Lake_DSL_declField___closed__10 = _init_l_Lake_DSL_declField___closed__10();
lean_mark_persistent(l_Lake_DSL_declField___closed__10);
l_Lake_DSL_declField___closed__11 = _init_l_Lake_DSL_declField___closed__11();
lean_mark_persistent(l_Lake_DSL_declField___closed__11);
l_Lake_DSL_declField___closed__12 = _init_l_Lake_DSL_declField___closed__12();
lean_mark_persistent(l_Lake_DSL_declField___closed__12);
l_Lake_DSL_declField___closed__13 = _init_l_Lake_DSL_declField___closed__13();
lean_mark_persistent(l_Lake_DSL_declField___closed__13);
l_Lake_DSL_declField___closed__14 = _init_l_Lake_DSL_declField___closed__14();
lean_mark_persistent(l_Lake_DSL_declField___closed__14);
l_Lake_DSL_declField___closed__15 = _init_l_Lake_DSL_declField___closed__15();
lean_mark_persistent(l_Lake_DSL_declField___closed__15);
l_Lake_DSL_declField___closed__16 = _init_l_Lake_DSL_declField___closed__16();
lean_mark_persistent(l_Lake_DSL_declField___closed__16);
l_Lake_DSL_declField___closed__17 = _init_l_Lake_DSL_declField___closed__17();
lean_mark_persistent(l_Lake_DSL_declField___closed__17);
l_Lake_DSL_declField = _init_l_Lake_DSL_declField();
lean_mark_persistent(l_Lake_DSL_declField);
l_Lake_DSL_structVal___closed__1 = _init_l_Lake_DSL_structVal___closed__1();
lean_mark_persistent(l_Lake_DSL_structVal___closed__1);
l_Lake_DSL_structVal___closed__2 = _init_l_Lake_DSL_structVal___closed__2();
lean_mark_persistent(l_Lake_DSL_structVal___closed__2);
l_Lake_DSL_structVal___closed__3 = _init_l_Lake_DSL_structVal___closed__3();
lean_mark_persistent(l_Lake_DSL_structVal___closed__3);
l_Lake_DSL_structVal___closed__4 = _init_l_Lake_DSL_structVal___closed__4();
lean_mark_persistent(l_Lake_DSL_structVal___closed__4);
l_Lake_DSL_structVal___closed__5 = _init_l_Lake_DSL_structVal___closed__5();
lean_mark_persistent(l_Lake_DSL_structVal___closed__5);
l_Lake_DSL_structVal___closed__6 = _init_l_Lake_DSL_structVal___closed__6();
lean_mark_persistent(l_Lake_DSL_structVal___closed__6);
l_Lake_DSL_structVal___closed__7 = _init_l_Lake_DSL_structVal___closed__7();
lean_mark_persistent(l_Lake_DSL_structVal___closed__7);
l_Lake_DSL_structVal___closed__8 = _init_l_Lake_DSL_structVal___closed__8();
lean_mark_persistent(l_Lake_DSL_structVal___closed__8);
l_Lake_DSL_structVal___closed__9 = _init_l_Lake_DSL_structVal___closed__9();
lean_mark_persistent(l_Lake_DSL_structVal___closed__9);
l_Lake_DSL_structVal___closed__10 = _init_l_Lake_DSL_structVal___closed__10();
lean_mark_persistent(l_Lake_DSL_structVal___closed__10);
l_Lake_DSL_structVal___closed__11 = _init_l_Lake_DSL_structVal___closed__11();
lean_mark_persistent(l_Lake_DSL_structVal___closed__11);
l_Lake_DSL_structVal___closed__12 = _init_l_Lake_DSL_structVal___closed__12();
lean_mark_persistent(l_Lake_DSL_structVal___closed__12);
l_Lake_DSL_structVal___closed__13 = _init_l_Lake_DSL_structVal___closed__13();
lean_mark_persistent(l_Lake_DSL_structVal___closed__13);
l_Lake_DSL_structVal___closed__14 = _init_l_Lake_DSL_structVal___closed__14();
lean_mark_persistent(l_Lake_DSL_structVal___closed__14);
l_Lake_DSL_structVal___closed__15 = _init_l_Lake_DSL_structVal___closed__15();
lean_mark_persistent(l_Lake_DSL_structVal___closed__15);
l_Lake_DSL_structVal___closed__16 = _init_l_Lake_DSL_structVal___closed__16();
lean_mark_persistent(l_Lake_DSL_structVal___closed__16);
l_Lake_DSL_structVal___closed__17 = _init_l_Lake_DSL_structVal___closed__17();
lean_mark_persistent(l_Lake_DSL_structVal___closed__17);
l_Lake_DSL_structVal___closed__18 = _init_l_Lake_DSL_structVal___closed__18();
lean_mark_persistent(l_Lake_DSL_structVal___closed__18);
l_Lake_DSL_structVal___closed__19 = _init_l_Lake_DSL_structVal___closed__19();
lean_mark_persistent(l_Lake_DSL_structVal___closed__19);
l_Lake_DSL_structVal___closed__20 = _init_l_Lake_DSL_structVal___closed__20();
lean_mark_persistent(l_Lake_DSL_structVal___closed__20);
l_Lake_DSL_structVal___closed__21 = _init_l_Lake_DSL_structVal___closed__21();
lean_mark_persistent(l_Lake_DSL_structVal___closed__21);
l_Lake_DSL_structVal = _init_l_Lake_DSL_structVal();
lean_mark_persistent(l_Lake_DSL_structVal);
l_Lake_DSL_declValDo___closed__1 = _init_l_Lake_DSL_declValDo___closed__1();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__1);
l_Lake_DSL_declValDo___closed__2 = _init_l_Lake_DSL_declValDo___closed__2();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__2);
l_Lake_DSL_declValDo___closed__3 = _init_l_Lake_DSL_declValDo___closed__3();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__3);
l_Lake_DSL_declValDo___closed__4 = _init_l_Lake_DSL_declValDo___closed__4();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__4);
l_Lake_DSL_declValDo___closed__5 = _init_l_Lake_DSL_declValDo___closed__5();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__5);
l_Lake_DSL_declValDo___closed__6 = _init_l_Lake_DSL_declValDo___closed__6();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__6);
l_Lake_DSL_declValDo___closed__7 = _init_l_Lake_DSL_declValDo___closed__7();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__7);
l_Lake_DSL_declValDo___closed__8 = _init_l_Lake_DSL_declValDo___closed__8();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__8);
l_Lake_DSL_declValDo___closed__9 = _init_l_Lake_DSL_declValDo___closed__9();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__9);
l_Lake_DSL_declValDo___closed__10 = _init_l_Lake_DSL_declValDo___closed__10();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__10);
l_Lake_DSL_declValDo___closed__11 = _init_l_Lake_DSL_declValDo___closed__11();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__11);
l_Lake_DSL_declValDo___closed__12 = _init_l_Lake_DSL_declValDo___closed__12();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__12);
l_Lake_DSL_declValDo___closed__13 = _init_l_Lake_DSL_declValDo___closed__13();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__13);
l_Lake_DSL_declValDo___closed__14 = _init_l_Lake_DSL_declValDo___closed__14();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__14);
l_Lake_DSL_declValDo___closed__15 = _init_l_Lake_DSL_declValDo___closed__15();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__15);
l_Lake_DSL_declValDo = _init_l_Lake_DSL_declValDo();
lean_mark_persistent(l_Lake_DSL_declValDo);
l_Lake_DSL_declValStruct___closed__1 = _init_l_Lake_DSL_declValStruct___closed__1();
lean_mark_persistent(l_Lake_DSL_declValStruct___closed__1);
l_Lake_DSL_declValStruct___closed__2 = _init_l_Lake_DSL_declValStruct___closed__2();
lean_mark_persistent(l_Lake_DSL_declValStruct___closed__2);
l_Lake_DSL_declValStruct___closed__3 = _init_l_Lake_DSL_declValStruct___closed__3();
lean_mark_persistent(l_Lake_DSL_declValStruct___closed__3);
l_Lake_DSL_declValStruct___closed__4 = _init_l_Lake_DSL_declValStruct___closed__4();
lean_mark_persistent(l_Lake_DSL_declValStruct___closed__4);
l_Lake_DSL_declValStruct___closed__5 = _init_l_Lake_DSL_declValStruct___closed__5();
lean_mark_persistent(l_Lake_DSL_declValStruct___closed__5);
l_Lake_DSL_declValStruct = _init_l_Lake_DSL_declValStruct();
lean_mark_persistent(l_Lake_DSL_declValStruct);
l_Lake_DSL_declValWhere___closed__1 = _init_l_Lake_DSL_declValWhere___closed__1();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__1);
l_Lake_DSL_declValWhere___closed__2 = _init_l_Lake_DSL_declValWhere___closed__2();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__2);
l_Lake_DSL_declValWhere___closed__3 = _init_l_Lake_DSL_declValWhere___closed__3();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__3);
l_Lake_DSL_declValWhere___closed__4 = _init_l_Lake_DSL_declValWhere___closed__4();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__4);
l_Lake_DSL_declValWhere___closed__5 = _init_l_Lake_DSL_declValWhere___closed__5();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__5);
l_Lake_DSL_declValWhere___closed__6 = _init_l_Lake_DSL_declValWhere___closed__6();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__6);
l_Lake_DSL_declValWhere___closed__7 = _init_l_Lake_DSL_declValWhere___closed__7();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__7);
l_Lake_DSL_declValWhere___closed__8 = _init_l_Lake_DSL_declValWhere___closed__8();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__8);
l_Lake_DSL_declValWhere___closed__9 = _init_l_Lake_DSL_declValWhere___closed__9();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__9);
l_Lake_DSL_declValWhere___closed__10 = _init_l_Lake_DSL_declValWhere___closed__10();
lean_mark_persistent(l_Lake_DSL_declValWhere___closed__10);
l_Lake_DSL_declValWhere = _init_l_Lake_DSL_declValWhere();
lean_mark_persistent(l_Lake_DSL_declValWhere);
l_Lake_DSL_declValTyped___closed__1 = _init_l_Lake_DSL_declValTyped___closed__1();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__1);
l_Lake_DSL_declValTyped___closed__2 = _init_l_Lake_DSL_declValTyped___closed__2();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__2);
l_Lake_DSL_declValTyped___closed__3 = _init_l_Lake_DSL_declValTyped___closed__3();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__3);
l_Lake_DSL_declValTyped___closed__4 = _init_l_Lake_DSL_declValTyped___closed__4();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__4);
l_Lake_DSL_declValTyped___closed__5 = _init_l_Lake_DSL_declValTyped___closed__5();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__5);
l_Lake_DSL_declValTyped___closed__6 = _init_l_Lake_DSL_declValTyped___closed__6();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__6);
l_Lake_DSL_declValTyped___closed__7 = _init_l_Lake_DSL_declValTyped___closed__7();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__7);
l_Lake_DSL_declValTyped___closed__8 = _init_l_Lake_DSL_declValTyped___closed__8();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__8);
l_Lake_DSL_declValTyped___closed__9 = _init_l_Lake_DSL_declValTyped___closed__9();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__9);
l_Lake_DSL_declValTyped___closed__10 = _init_l_Lake_DSL_declValTyped___closed__10();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__10);
l_Lake_DSL_declValTyped___closed__11 = _init_l_Lake_DSL_declValTyped___closed__11();
lean_mark_persistent(l_Lake_DSL_declValTyped___closed__11);
l_Lake_DSL_declValTyped = _init_l_Lake_DSL_declValTyped();
lean_mark_persistent(l_Lake_DSL_declValTyped);
l_Lake_DSL_declValOptTyped___closed__1 = _init_l_Lake_DSL_declValOptTyped___closed__1();
lean_mark_persistent(l_Lake_DSL_declValOptTyped___closed__1);
l_Lake_DSL_declValOptTyped___closed__2 = _init_l_Lake_DSL_declValOptTyped___closed__2();
lean_mark_persistent(l_Lake_DSL_declValOptTyped___closed__2);
l_Lake_DSL_declValOptTyped___closed__3 = _init_l_Lake_DSL_declValOptTyped___closed__3();
lean_mark_persistent(l_Lake_DSL_declValOptTyped___closed__3);
l_Lake_DSL_declValOptTyped___closed__4 = _init_l_Lake_DSL_declValOptTyped___closed__4();
lean_mark_persistent(l_Lake_DSL_declValOptTyped___closed__4);
l_Lake_DSL_declValOptTyped___closed__5 = _init_l_Lake_DSL_declValOptTyped___closed__5();
lean_mark_persistent(l_Lake_DSL_declValOptTyped___closed__5);
l_Lake_DSL_declValOptTyped = _init_l_Lake_DSL_declValOptTyped();
lean_mark_persistent(l_Lake_DSL_declValOptTyped);
l_Lake_DSL_simpleDeclSig___closed__1 = _init_l_Lake_DSL_simpleDeclSig___closed__1();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__1);
l_Lake_DSL_simpleDeclSig___closed__2 = _init_l_Lake_DSL_simpleDeclSig___closed__2();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__2);
l_Lake_DSL_simpleDeclSig___closed__3 = _init_l_Lake_DSL_simpleDeclSig___closed__3();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__3);
l_Lake_DSL_simpleDeclSig___closed__4 = _init_l_Lake_DSL_simpleDeclSig___closed__4();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__4);
l_Lake_DSL_simpleDeclSig___closed__5 = _init_l_Lake_DSL_simpleDeclSig___closed__5();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__5);
l_Lake_DSL_simpleDeclSig = _init_l_Lake_DSL_simpleDeclSig();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig);
l_Lake_DSL_structDeclSig___closed__1 = _init_l_Lake_DSL_structDeclSig___closed__1();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__1);
l_Lake_DSL_structDeclSig___closed__2 = _init_l_Lake_DSL_structDeclSig___closed__2();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__2);
l_Lake_DSL_structDeclSig___closed__3 = _init_l_Lake_DSL_structDeclSig___closed__3();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__3);
l_Lake_DSL_structDeclSig___closed__4 = _init_l_Lake_DSL_structDeclSig___closed__4();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__4);
l_Lake_DSL_structDeclSig___closed__5 = _init_l_Lake_DSL_structDeclSig___closed__5();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__5);
l_Lake_DSL_structDeclSig___closed__6 = _init_l_Lake_DSL_structDeclSig___closed__6();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__6);
l_Lake_DSL_structDeclSig___closed__7 = _init_l_Lake_DSL_structDeclSig___closed__7();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__7);
l_Lake_DSL_structDeclSig___closed__8 = _init_l_Lake_DSL_structDeclSig___closed__8();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__8);
l_Lake_DSL_structDeclSig___closed__9 = _init_l_Lake_DSL_structDeclSig___closed__9();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__9);
l_Lake_DSL_structDeclSig = _init_l_Lake_DSL_structDeclSig();
lean_mark_persistent(l_Lake_DSL_structDeclSig);
l_Lake_DSL_bracketedSimpleBinder___closed__1 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__1();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__1);
l_Lake_DSL_bracketedSimpleBinder___closed__2 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__2();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__2);
l_Lake_DSL_bracketedSimpleBinder___closed__3 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__3();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__3);
l_Lake_DSL_bracketedSimpleBinder___closed__4 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__4();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__4);
l_Lake_DSL_bracketedSimpleBinder___closed__5 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__5();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__5);
l_Lake_DSL_bracketedSimpleBinder___closed__6 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__6();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__6);
l_Lake_DSL_bracketedSimpleBinder___closed__7 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__7();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__7);
l_Lake_DSL_bracketedSimpleBinder___closed__8 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__8();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__8);
l_Lake_DSL_bracketedSimpleBinder___closed__9 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__9();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__9);
l_Lake_DSL_bracketedSimpleBinder___closed__10 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__10();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__10);
l_Lake_DSL_bracketedSimpleBinder___closed__11 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__11();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__11);
l_Lake_DSL_bracketedSimpleBinder___closed__12 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__12();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__12);
l_Lake_DSL_bracketedSimpleBinder___closed__13 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__13();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__13);
l_Lake_DSL_bracketedSimpleBinder___closed__14 = _init_l_Lake_DSL_bracketedSimpleBinder___closed__14();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder___closed__14);
l_Lake_DSL_bracketedSimpleBinder = _init_l_Lake_DSL_bracketedSimpleBinder();
lean_mark_persistent(l_Lake_DSL_bracketedSimpleBinder);
l_Lake_DSL_simpleBinder___closed__1 = _init_l_Lake_DSL_simpleBinder___closed__1();
lean_mark_persistent(l_Lake_DSL_simpleBinder___closed__1);
l_Lake_DSL_simpleBinder___closed__2 = _init_l_Lake_DSL_simpleBinder___closed__2();
lean_mark_persistent(l_Lake_DSL_simpleBinder___closed__2);
l_Lake_DSL_simpleBinder___closed__3 = _init_l_Lake_DSL_simpleBinder___closed__3();
lean_mark_persistent(l_Lake_DSL_simpleBinder___closed__3);
l_Lake_DSL_simpleBinder___closed__4 = _init_l_Lake_DSL_simpleBinder___closed__4();
lean_mark_persistent(l_Lake_DSL_simpleBinder___closed__4);
l_Lake_DSL_simpleBinder = _init_l_Lake_DSL_simpleBinder();
lean_mark_persistent(l_Lake_DSL_simpleBinder);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7);
l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8 = _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8();
lean_mark_persistent(l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8);
l_Lake_DSL_expandDeclField___closed__1 = _init_l_Lake_DSL_expandDeclField___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__1);
l_Lake_DSL_expandDeclField___closed__2 = _init_l_Lake_DSL_expandDeclField___closed__2();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__2);
l_Lake_DSL_expandDeclField___closed__3 = _init_l_Lake_DSL_expandDeclField___closed__3();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__3);
l_Lake_DSL_expandDeclField___closed__4 = _init_l_Lake_DSL_expandDeclField___closed__4();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__4);
l_Lake_DSL_expandDeclField___closed__5 = _init_l_Lake_DSL_expandDeclField___closed__5();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__5);
l_Lake_DSL_expandDeclField___closed__6 = _init_l_Lake_DSL_expandDeclField___closed__6();
lean_mark_persistent(l_Lake_DSL_expandDeclField___closed__6);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__1 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__1();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__1);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__2 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__2();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__2);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__3 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__3();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__3);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__4 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__4();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__4);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__5 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__5();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__5);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__6 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__6();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__6);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__7 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__7();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__7);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__8 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__8();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__8);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__9 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__9();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__9);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__10 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__10();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__10);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__11 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__11();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__11);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__12 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__12();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__12);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__13 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__13();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__13);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__14 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__14();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__14);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__15 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__15();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__15);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__16 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__16();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__16);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__17 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__17();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__17);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__18 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__18();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__18);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__19 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__19();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__19);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__20 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__20();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__20);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__21 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__21();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__21);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__22 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__22();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__22);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__23 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__23();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__23);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__24 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__24();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__24);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__25 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__25();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__25);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__26 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__26();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__26);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__27 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__27();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__27);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__28 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__28();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__28);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__29 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__29();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__29);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__30 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__30();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__30);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__31 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__31();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__31);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__32 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__32();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__32);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__33 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__33();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__33);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__34 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__34();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__34);
l_Lake_DSL_mkConfigDecl___lambda__3___closed__35 = _init_l_Lake_DSL_mkConfigDecl___lambda__3___closed__35();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__3___closed__35);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__1 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__1();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__1);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__2 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__2();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__2);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__3 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__3();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__3);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__4 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__4();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__4);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__5 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__5();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__5);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__6 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__6();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__6);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__7 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__7();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__7);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__8 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__8();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__8);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__9 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__9();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__9);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__10 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__10();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__10);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__11 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__11();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__11);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__12 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__12();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__12);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__13 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__13();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__13);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__14 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__14();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__14);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__15 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__15();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__15);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__16 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__16();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__16);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__17 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__17();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__17);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__18 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__18();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__18);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__19 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__19();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__19);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__20 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__20();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__20);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__21 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__21();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__21);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__22 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__22();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__22);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__23 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__23();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__23);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__24 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__24();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__24);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__25 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__25();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__25);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__26 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__26();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__26);
l_Lake_DSL_mkConfigDecl___lambda__4___closed__27 = _init_l_Lake_DSL_mkConfigDecl___lambda__4___closed__27();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___lambda__4___closed__27);
l_Lake_DSL_mkConfigDecl___closed__1 = _init_l_Lake_DSL_mkConfigDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_mkConfigDecl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
