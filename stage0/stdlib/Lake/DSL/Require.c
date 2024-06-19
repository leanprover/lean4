// Lean compiler output
// Module: Lake.DSL.Require
// Imports: Init Lean.Parser.Command Lake.Config.Dependency Lake.DSL.Extensions Lake.DSL.DeclUtil
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
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_depSpec;
static lean_object* l_Lake_DSL_fromGit___closed__8;
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__2;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__73;
static lean_object* l_Lake_DSL_depSpec___closed__2;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__26;
lean_object* l_Lean_Macro_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__19;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_DSL_depSpec___closed__9;
static lean_object* l_Lake_DSL_requireDecl___closed__6;
static lean_object* l_Lake_DSL_requireDecl___closed__11;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__65;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__5;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__63;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__11;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__11;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__62;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__53;
static lean_object* l_Lake_DSL_depSpec___closed__18;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__41;
static lean_object* l_Lake_DSL_fromGit___closed__18;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_requireDecl;
static lean_object* l_Lake_DSL_fromPath___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__23;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__82;
static lean_object* l_Lake_DSL_depSpec___closed__8;
static lean_object* l_Lake_DSL_depSpec___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__67;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__9;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__42;
static lean_object* l_Lake_DSL_expandDepSpec___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__81;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__69;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__58;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__48;
static lean_object* l_Lake_DSL_fromGit___closed__2;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__6;
static lean_object* l_Lake_DSL_expandDepSpec___closed__2;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__35;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__75;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__70;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
static lean_object* l_Lake_DSL_requireDecl___closed__5;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__47;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__6;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__4;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__24;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__55;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__59;
static lean_object* l_Lake_DSL_requireDecl___closed__9;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__36;
static lean_object* l_Lake_DSL_fromGit___closed__12;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__28;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__78;
static lean_object* l_Lake_DSL_fromGit___closed__20;
static lean_object* l_Lake_DSL_requireDecl___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__16;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__66;
static lean_object* l_Lake_DSL_fromGit___closed__5;
static lean_object* l_Lake_DSL_requireDecl___closed__2;
static lean_object* l_Lake_DSL_depSpec___closed__15;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__10;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__29;
static lean_object* l_Lake_DSL_fromPath___closed__5;
static lean_object* l_Lake_DSL_fromPath___closed__4;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__8;
static lean_object* l_Lake_DSL_depSpec___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__56;
static lean_object* l_Lake_DSL_requireDecl___closed__10;
static lean_object* l_Lake_DSL_fromGit___closed__14;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__71;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromPath___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__5;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__2;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__3;
static lean_object* l_Lake_DSL_fromGit___closed__6;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__38;
static lean_object* l_Lake_DSL_fromGit___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__44;
static lean_object* l_Lake_DSL_fromGit___closed__10;
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_quoteNameMk(lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__10;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__12;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__33;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__80;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__50;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__77;
static lean_object* l_Lake_DSL_depSpec___closed__14;
LEAN_EXPORT lean_object* l_Lake_DSL_fromGit;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__13;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__34;
static lean_object* l_Lake_DSL_depSpec___closed__11;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__15;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__16;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__40;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__22;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__14;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_depSpec___closed__6;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__3;
static lean_object* l_Lake_DSL_requireDecl___closed__4;
static lean_object* l_Lake_DSL_fromPath___closed__6;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__43;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__8;
static lean_object* l_Lake_DSL_depSpec___closed__10;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__4;
static lean_object* l_Lake_DSL_fromGit___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_fromPath;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__15;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__5;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__64;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Require______macroRules__Lake__DSL__requireDecl__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__21;
static lean_object* l_Lake_DSL_fromGit___closed__13;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__74;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__46;
static lean_object* l_Lake_DSL_requireDecl___closed__8;
static lean_object* l_Lake_DSL_fromGit___closed__21;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__3;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromPath___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__32;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__57;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__84;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__79;
static lean_object* l_Lake_DSL_fromGit___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__72;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__11;
static lean_object* l_Lake_DSL_depSpec___closed__16;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__83;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lake_DSL_fromGit___closed__4;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__52;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__60;
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__31;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__30;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__12;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__6;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_fromPath___closed__8;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__25;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__2;
static lean_object* l_Lake_DSL_depSpec___closed__13;
static lean_object* l_Lake_DSL_fromGit___closed__17;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__19;
static lean_object* l_Lake_DSL_expandDepSpec___closed__3;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__54;
static lean_object* l_Lake_DSL_fromPath___closed__3;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__18;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__4;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__61;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__37;
static lean_object* l_Lake_DSL_depSpec___closed__17;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_depSpec___closed__3;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__3___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__45;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_depSpec___closed__12;
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_depSpec___closed__1;
static lean_object* l_Lake_DSL_requireDecl___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__27;
static lean_object* l_Lake_DSL_depSpec___closed__4;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__9;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__68;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__51;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__76;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__2___closed__1;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__49;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__20;
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand(lean_object*);
static lean_object* l_Lake_DSL_requireDecl___closed__3;
static lean_object* l_Lake_DSL_expandDepSpec___lambda__1___closed__39;
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___boxed(lean_object*);
static lean_object* _init_l_Lake_DSL_fromPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("DSL", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fromPath", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_fromPath___closed__2;
x_3 = l_Lake_DSL_fromPath___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_fromPath___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromPath___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromPath___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__3;
x_2 = l_Lake_DSL_fromPath___closed__4;
x_3 = l_Lake_DSL_fromPath___closed__7;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromPath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromPath___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fromGit", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_fromPath___closed__2;
x_3 = l_Lake_DSL_fromGit___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_fromGit___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" git ", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromPath___closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__6;
x_3 = l_Lake_DSL_fromGit___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optional", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_fromGit___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromGit___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__12;
x_3 = l_Lake_DSL_fromGit___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__10;
x_2 = l_Lake_DSL_fromGit___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__8;
x_3 = l_Lake_DSL_fromGit___closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_fromGit___closed__16;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__17;
x_3 = l_Lake_DSL_fromPath___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__10;
x_2 = l_Lake_DSL_fromGit___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_fromGit___closed__15;
x_3 = l_Lake_DSL_fromGit___closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__1;
x_2 = l_Lake_DSL_fromGit___closed__2;
x_3 = l_Lake_DSL_fromGit___closed__20;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_fromGit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_fromGit___closed__21;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("depSpec", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_fromPath___closed__2;
x_3 = l_Lake_DSL_depSpec___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_depSpec___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depSpec___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" from ", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depSpec___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_depSpec___closed__5;
x_3 = l_Lake_DSL_depSpec___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("orelse", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_depSpec___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__10;
x_2 = l_Lake_DSL_fromGit;
x_3 = l_Lake_DSL_fromPath;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_depSpec___closed__8;
x_3 = l_Lake_DSL_depSpec___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" with ", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_depSpec___closed__13;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_depSpec___closed__14;
x_3 = l_Lake_DSL_fromPath___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__10;
x_2 = l_Lake_DSL_depSpec___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_depSpec___closed__12;
x_3 = l_Lake_DSL_depSpec___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_depSpec___closed__1;
x_2 = l_Lake_DSL_depSpec___closed__2;
x_3 = l_Lake_DSL_depSpec___closed__17;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_depSpec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_depSpec___closed__18;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("choice", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term{}", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInst", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optEllipsis", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__18;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declModifiers", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__20;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attributes", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__22;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrInstance", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrKind", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__27;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attr", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simple", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__29;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__30;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("package_dep", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__32;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__32;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__36;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declId", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__39;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__14;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optDeclSig", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__43;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeSpec", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__45;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declValSimple", 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__17;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__48;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstField", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__51;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstLVal", 14);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__53;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__55;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__55;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__58() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("src", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__59;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__59;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__62;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__64() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Source.path", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__64;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__66() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Source", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__67() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("path", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__66;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__67;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__66;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__67;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__69;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__69;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__71;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__70;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__72;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__74() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("opts", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__74;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__74;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__77() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Termination", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__78() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("suffix", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__77;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__78;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quotedName", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__7;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__8;
x_3 = l_Lake_DSL_expandDepSpec___lambda__1___closed__9;
x_4 = l_Lake_DSL_expandDepSpec___lambda__1___closed__80;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__82() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
x_10 = 0;
x_11 = l_Lean_SourceInfo_fromRef(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lake_DSL_expandDepSpec___lambda__1___closed__5;
lean_inc(x_11);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_DSL_expandDepSpec___lambda__1___closed__6;
lean_inc(x_11);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lake_DSL_expandDepSpec___lambda__1___closed__4;
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_11);
x_17 = l_Lean_Syntax_node2(x_11, x_16, x_13, x_15);
x_18 = l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
x_19 = l_Lake_DSL_expandDepSpec___lambda__1___closed__14;
lean_inc(x_11);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lake_DSL_expandDepSpec___lambda__1___closed__16;
lean_inc(x_20);
lean_inc(x_11);
x_22 = l_Lean_Syntax_node1(x_11, x_21, x_20);
x_23 = l_Lake_DSL_expandDepSpec___lambda__1___closed__11;
lean_inc(x_15);
lean_inc(x_22);
lean_inc_n(x_20, 3);
lean_inc(x_13);
lean_inc(x_11);
x_24 = l_Lean_Syntax_node6(x_11, x_23, x_13, x_20, x_20, x_22, x_20, x_15);
x_25 = l_Lake_DSL_expandDepSpec___lambda__1___closed__2;
lean_inc(x_11);
x_26 = l_Lean_Syntax_node2(x_11, x_25, x_17, x_24);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = l_Lake_DSL_expandDepSpec___lambda__1___closed__24;
lean_inc(x_11);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lake_DSL_expandDepSpec___lambda__1___closed__28;
lean_inc(x_20);
lean_inc(x_11);
x_32 = l_Lean_Syntax_node1(x_11, x_31, x_20);
x_33 = l_Lake_DSL_expandDepSpec___lambda__1___closed__34;
lean_inc(x_27);
lean_inc(x_28);
x_34 = l_Lean_addMacroScope(x_28, x_33, x_27);
x_35 = lean_box(0);
x_36 = l_Lake_DSL_expandDepSpec___lambda__1___closed__33;
lean_inc(x_11);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
x_38 = l_Lake_DSL_expandDepSpec___lambda__1___closed__31;
lean_inc(x_20);
lean_inc(x_11);
x_39 = l_Lean_Syntax_node2(x_11, x_38, x_37, x_20);
x_40 = l_Lake_DSL_expandDepSpec___lambda__1___closed__26;
lean_inc(x_11);
x_41 = l_Lean_Syntax_node2(x_11, x_40, x_32, x_39);
lean_inc(x_11);
x_42 = l_Lean_Syntax_node1(x_11, x_18, x_41);
x_43 = l_Lake_DSL_expandDepSpec___lambda__1___closed__35;
lean_inc(x_11);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lake_DSL_expandDepSpec___lambda__1___closed__23;
lean_inc(x_11);
x_46 = l_Lean_Syntax_node3(x_11, x_45, x_30, x_42, x_44);
lean_inc(x_11);
x_47 = l_Lean_Syntax_node1(x_11, x_18, x_46);
x_48 = l_Lake_DSL_expandDepSpec___lambda__1___closed__38;
lean_inc(x_11);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lake_DSL_expandDepSpec___lambda__1___closed__42;
lean_inc(x_1);
x_51 = lean_array_push(x_50, x_1);
x_52 = l_Lake_DSL_expandDepSpec___lambda__1___closed__41;
x_53 = lean_array_push(x_51, x_52);
x_54 = lean_box(2);
x_55 = l_Lake_DSL_expandDepSpec___lambda__1___closed__40;
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
x_57 = l_Lake_DSL_expandDepSpec___lambda__1___closed__47;
lean_inc(x_11);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lake_DSL_expandDepSpec___lambda__1___closed__46;
lean_inc(x_11);
x_60 = l_Lean_Syntax_node2(x_11, x_59, x_58, x_2);
lean_inc(x_11);
x_61 = l_Lean_Syntax_node1(x_11, x_18, x_60);
x_62 = l_Lake_DSL_expandDepSpec___lambda__1___closed__44;
lean_inc(x_20);
lean_inc(x_11);
x_63 = l_Lean_Syntax_node2(x_11, x_62, x_20, x_61);
x_64 = l_Lake_DSL_expandDepSpec___lambda__1___closed__50;
lean_inc(x_11);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lake_DSL_expandDepSpec___lambda__1___closed__57;
lean_inc(x_27);
lean_inc(x_28);
x_67 = l_Lean_addMacroScope(x_28, x_66, x_27);
x_68 = l_Lake_DSL_expandDepSpec___lambda__1___closed__56;
lean_inc(x_11);
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_11);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_69, 3, x_35);
x_70 = l_Lake_DSL_expandDepSpec___lambda__1___closed__54;
lean_inc(x_20);
lean_inc(x_11);
x_71 = l_Lean_Syntax_node2(x_11, x_70, x_69, x_20);
x_72 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
lean_inc(x_72);
x_73 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_35, x_72);
x_74 = l_Lake_DSL_expandDepSpec___lambda__1___closed__58;
lean_inc(x_11);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_DSL_expandDepSpec___lambda__1___closed__61;
lean_inc(x_27);
lean_inc(x_28);
x_77 = l_Lean_addMacroScope(x_28, x_76, x_27);
x_78 = l_Lake_DSL_expandDepSpec___lambda__1___closed__60;
lean_inc(x_11);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_11);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_35);
lean_inc(x_20);
lean_inc(x_11);
x_80 = l_Lean_Syntax_node2(x_11, x_70, x_79, x_20);
x_81 = l_Lake_DSL_expandDepSpec___lambda__1___closed__68;
lean_inc(x_27);
lean_inc(x_28);
x_82 = l_Lean_addMacroScope(x_28, x_81, x_27);
x_83 = l_Lake_DSL_expandDepSpec___lambda__1___closed__65;
x_84 = l_Lake_DSL_expandDepSpec___lambda__1___closed__73;
lean_inc(x_11);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_11);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_84);
lean_inc(x_11);
x_86 = l_Lean_Syntax_node1(x_11, x_18, x_3);
x_87 = l_Lake_DSL_expandDepSpec___lambda__1___closed__63;
lean_inc(x_11);
x_88 = l_Lean_Syntax_node2(x_11, x_87, x_85, x_86);
x_89 = l_Lake_DSL_expandDepSpec___lambda__1___closed__52;
lean_inc(x_65);
lean_inc(x_11);
x_90 = l_Lean_Syntax_node3(x_11, x_89, x_80, x_65, x_88);
x_91 = l_Lake_DSL_expandDepSpec___lambda__1___closed__76;
x_92 = l_Lean_addMacroScope(x_28, x_91, x_27);
x_93 = l_Lake_DSL_expandDepSpec___lambda__1___closed__75;
lean_inc(x_11);
x_94 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_35);
lean_inc(x_20);
lean_inc(x_11);
x_95 = l_Lean_Syntax_node2(x_11, x_70, x_94, x_20);
x_96 = l_Lake_DSL_expandDepSpec___lambda__1___closed__79;
lean_inc_n(x_20, 2);
lean_inc(x_11);
x_97 = l_Lean_Syntax_node2(x_11, x_96, x_20, x_20);
if (lean_obj_tag(x_6) == 0)
{
x_98 = x_26;
goto block_139;
}
else
{
lean_object* x_140; 
lean_dec(x_26);
x_140 = lean_ctor_get(x_6, 0);
lean_inc(x_140);
lean_dec(x_6);
x_98 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_99; lean_object* x_100; 
lean_inc(x_65);
lean_inc(x_11);
x_99 = l_Lean_Syntax_node3(x_11, x_89, x_95, x_65, x_98);
if (lean_obj_tag(x_4) == 0)
{
x_100 = x_19;
goto block_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_4, 0);
lean_inc(x_137);
lean_dec(x_4);
x_138 = l_Array_mkArray1___rarg(x_137);
x_100 = x_138;
goto block_136;
}
block_136:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = l_Array_append___rarg(x_19, x_100);
lean_dec(x_100);
lean_inc(x_11);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_11);
lean_ctor_set(x_102, 1, x_18);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lake_DSL_expandDepSpec___lambda__1___closed__21;
lean_inc_n(x_20, 4);
lean_inc(x_11);
x_104 = l_Lean_Syntax_node6(x_11, x_103, x_102, x_47, x_20, x_20, x_20, x_20);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = l_Lean_quoteNameMk(x_72);
lean_inc(x_65);
lean_inc(x_11);
x_106 = l_Lean_Syntax_node3(x_11, x_89, x_71, x_65, x_105);
lean_inc(x_75);
lean_inc(x_11);
x_107 = l_Lean_Syntax_node5(x_11, x_18, x_106, x_75, x_90, x_75, x_99);
lean_inc_n(x_20, 2);
lean_inc(x_11);
x_108 = l_Lean_Syntax_node6(x_11, x_23, x_13, x_20, x_107, x_22, x_20, x_15);
x_109 = l_Lake_DSL_expandDepSpec___lambda__1___closed__49;
lean_inc(x_20);
lean_inc(x_11);
x_110 = l_Lean_Syntax_node4(x_11, x_109, x_65, x_108, x_97, x_20);
x_111 = l_Lake_DSL_expandDepSpec___lambda__1___closed__37;
lean_inc(x_11);
x_112 = l_Lean_Syntax_node5(x_11, x_111, x_49, x_56, x_63, x_110, x_20);
x_113 = l_Lake_DSL_expandDepSpec___lambda__1___closed__19;
x_114 = l_Lean_Syntax_node2(x_11, x_113, x_104, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_8);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_72);
x_116 = lean_ctor_get(x_73, 0);
lean_inc(x_116);
lean_dec(x_73);
x_117 = l_Lake_DSL_expandDepSpec___lambda__1___closed__82;
x_118 = l_String_intercalate(x_117, x_116);
x_119 = l_Lake_DSL_expandDepSpec___lambda__1___closed__83;
x_120 = lean_string_append(x_119, x_118);
lean_dec(x_118);
x_121 = l_Lean_Syntax_mkNameLit(x_120, x_54);
x_122 = l_Lake_DSL_expandDepSpec___lambda__1___closed__84;
x_123 = lean_array_push(x_122, x_121);
x_124 = l_Lake_DSL_expandDepSpec___lambda__1___closed__81;
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_54);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_123);
lean_inc(x_65);
lean_inc(x_11);
x_126 = l_Lean_Syntax_node3(x_11, x_89, x_71, x_65, x_125);
lean_inc(x_75);
lean_inc(x_11);
x_127 = l_Lean_Syntax_node5(x_11, x_18, x_126, x_75, x_90, x_75, x_99);
lean_inc_n(x_20, 2);
lean_inc(x_11);
x_128 = l_Lean_Syntax_node6(x_11, x_23, x_13, x_20, x_127, x_22, x_20, x_15);
x_129 = l_Lake_DSL_expandDepSpec___lambda__1___closed__49;
lean_inc(x_20);
lean_inc(x_11);
x_130 = l_Lean_Syntax_node4(x_11, x_129, x_65, x_128, x_97, x_20);
x_131 = l_Lake_DSL_expandDepSpec___lambda__1___closed__37;
lean_inc(x_11);
x_132 = l_Lean_Syntax_node5(x_11, x_131, x_49, x_56, x_63, x_130, x_20);
x_133 = l_Lake_DSL_expandDepSpec___lambda__1___closed__19;
x_134 = l_Lean_Syntax_node2(x_11, x_133, x_104, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_8);
return x_135;
}
}
}
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Source.git", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__2___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("git", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__1___closed__66;
x_2 = l_Lake_DSL_expandDepSpec___lambda__2___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_expandDepSpec___lambda__1___closed__66;
x_3 = l_Lake_DSL_expandDepSpec___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__2___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__2___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__2___closed__6;
x_2 = l_Lake_DSL_expandDepSpec___lambda__2___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_10 = lean_ctor_get(x_8, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lake_DSL_expandDepSpec___lambda__1___closed__5;
lean_inc(x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lake_DSL_expandDepSpec___lambda__1___closed__6;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lake_DSL_expandDepSpec___lambda__1___closed__4;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_12);
x_18 = l_Lean_Syntax_node2(x_12, x_17, x_14, x_16);
x_19 = l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
x_20 = l_Lake_DSL_expandDepSpec___lambda__1___closed__14;
lean_inc(x_12);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lake_DSL_expandDepSpec___lambda__1___closed__16;
lean_inc(x_21);
lean_inc(x_12);
x_23 = l_Lean_Syntax_node1(x_12, x_22, x_21);
x_24 = l_Lake_DSL_expandDepSpec___lambda__1___closed__11;
lean_inc(x_16);
lean_inc(x_23);
lean_inc_n(x_21, 3);
lean_inc(x_14);
lean_inc(x_12);
x_25 = l_Lean_Syntax_node6(x_12, x_24, x_14, x_21, x_21, x_23, x_21, x_16);
x_26 = l_Lake_DSL_expandDepSpec___lambda__1___closed__2;
lean_inc(x_12);
x_27 = l_Lean_Syntax_node2(x_12, x_26, x_18, x_25);
x_28 = lean_ctor_get(x_8, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lake_DSL_expandDepSpec___lambda__1___closed__24;
lean_inc(x_12);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lake_DSL_expandDepSpec___lambda__1___closed__28;
lean_inc(x_21);
lean_inc(x_12);
x_33 = l_Lean_Syntax_node1(x_12, x_32, x_21);
x_34 = l_Lake_DSL_expandDepSpec___lambda__1___closed__34;
lean_inc(x_28);
lean_inc(x_29);
x_35 = l_Lean_addMacroScope(x_29, x_34, x_28);
x_36 = lean_box(0);
x_37 = l_Lake_DSL_expandDepSpec___lambda__1___closed__33;
lean_inc(x_12);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = l_Lake_DSL_expandDepSpec___lambda__1___closed__31;
lean_inc(x_21);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node2(x_12, x_39, x_38, x_21);
x_41 = l_Lake_DSL_expandDepSpec___lambda__1___closed__26;
lean_inc(x_12);
x_42 = l_Lean_Syntax_node2(x_12, x_41, x_33, x_40);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_19, x_42);
x_44 = l_Lake_DSL_expandDepSpec___lambda__1___closed__35;
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_DSL_expandDepSpec___lambda__1___closed__23;
lean_inc(x_12);
x_47 = l_Lean_Syntax_node3(x_12, x_46, x_31, x_43, x_45);
lean_inc(x_12);
x_48 = l_Lean_Syntax_node1(x_12, x_19, x_47);
x_49 = l_Lake_DSL_expandDepSpec___lambda__1___closed__38;
lean_inc(x_12);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_12);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lake_DSL_expandDepSpec___lambda__1___closed__42;
lean_inc(x_1);
x_52 = lean_array_push(x_51, x_1);
x_53 = l_Lake_DSL_expandDepSpec___lambda__1___closed__41;
x_54 = lean_array_push(x_52, x_53);
x_55 = lean_box(2);
x_56 = l_Lake_DSL_expandDepSpec___lambda__1___closed__40;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_54);
x_58 = l_Lake_DSL_expandDepSpec___lambda__1___closed__47;
lean_inc(x_12);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lake_DSL_expandDepSpec___lambda__1___closed__46;
lean_inc(x_12);
x_61 = l_Lean_Syntax_node2(x_12, x_60, x_59, x_2);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_19, x_61);
x_63 = l_Lake_DSL_expandDepSpec___lambda__1___closed__44;
lean_inc(x_21);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_63, x_21, x_62);
x_65 = l_Lake_DSL_expandDepSpec___lambda__1___closed__50;
lean_inc(x_12);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_12);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lake_DSL_expandDepSpec___lambda__1___closed__57;
lean_inc(x_28);
lean_inc(x_29);
x_68 = l_Lean_addMacroScope(x_29, x_67, x_28);
x_69 = l_Lake_DSL_expandDepSpec___lambda__1___closed__56;
lean_inc(x_12);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_36);
x_71 = l_Lake_DSL_expandDepSpec___lambda__1___closed__54;
lean_inc(x_21);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node2(x_12, x_71, x_70, x_21);
x_73 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
lean_inc(x_73);
x_74 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_36, x_73);
x_75 = l_Lake_DSL_expandDepSpec___lambda__1___closed__58;
lean_inc(x_12);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_12);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lake_DSL_expandDepSpec___lambda__1___closed__61;
lean_inc(x_28);
lean_inc(x_29);
x_78 = l_Lean_addMacroScope(x_29, x_77, x_28);
x_79 = l_Lake_DSL_expandDepSpec___lambda__1___closed__60;
lean_inc(x_12);
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_80, 3, x_36);
lean_inc(x_21);
lean_inc(x_12);
x_81 = l_Lean_Syntax_node2(x_12, x_71, x_80, x_21);
x_82 = l_Lake_DSL_expandDepSpec___lambda__2___closed__4;
lean_inc(x_28);
lean_inc(x_29);
x_83 = l_Lean_addMacroScope(x_29, x_82, x_28);
x_84 = l_Lake_DSL_expandDepSpec___lambda__2___closed__2;
x_85 = l_Lake_DSL_expandDepSpec___lambda__2___closed__9;
lean_inc(x_12);
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_85);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node3(x_12, x_19, x_3, x_4, x_7);
x_88 = l_Lake_DSL_expandDepSpec___lambda__1___closed__63;
lean_inc(x_12);
x_89 = l_Lean_Syntax_node2(x_12, x_88, x_86, x_87);
x_90 = l_Lake_DSL_expandDepSpec___lambda__1___closed__52;
lean_inc(x_66);
lean_inc(x_12);
x_91 = l_Lean_Syntax_node3(x_12, x_90, x_81, x_66, x_89);
x_92 = l_Lake_DSL_expandDepSpec___lambda__1___closed__76;
x_93 = l_Lean_addMacroScope(x_29, x_92, x_28);
x_94 = l_Lake_DSL_expandDepSpec___lambda__1___closed__75;
lean_inc(x_12);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
lean_ctor_set(x_95, 3, x_36);
lean_inc(x_21);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node2(x_12, x_71, x_95, x_21);
x_97 = l_Lake_DSL_expandDepSpec___lambda__1___closed__79;
lean_inc_n(x_21, 2);
lean_inc(x_12);
x_98 = l_Lean_Syntax_node2(x_12, x_97, x_21, x_21);
if (lean_obj_tag(x_6) == 0)
{
x_99 = x_27;
goto block_140;
}
else
{
lean_object* x_141; 
lean_dec(x_27);
x_141 = lean_ctor_get(x_6, 0);
lean_inc(x_141);
lean_dec(x_6);
x_99 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_100; lean_object* x_101; 
lean_inc(x_66);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node3(x_12, x_90, x_96, x_66, x_99);
if (lean_obj_tag(x_5) == 0)
{
x_101 = x_20;
goto block_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_5, 0);
lean_inc(x_138);
lean_dec(x_5);
x_139 = l_Array_mkArray1___rarg(x_138);
x_101 = x_139;
goto block_137;
}
block_137:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = l_Array_append___rarg(x_20, x_101);
lean_dec(x_101);
lean_inc(x_12);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_12);
lean_ctor_set(x_103, 1, x_19);
lean_ctor_set(x_103, 2, x_102);
x_104 = l_Lake_DSL_expandDepSpec___lambda__1___closed__21;
lean_inc_n(x_21, 4);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node6(x_12, x_104, x_103, x_48, x_21, x_21, x_21, x_21);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_106 = l_Lean_quoteNameMk(x_73);
lean_inc(x_66);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node3(x_12, x_90, x_72, x_66, x_106);
lean_inc(x_76);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node5(x_12, x_19, x_107, x_76, x_91, x_76, x_100);
lean_inc_n(x_21, 2);
lean_inc(x_12);
x_109 = l_Lean_Syntax_node6(x_12, x_24, x_14, x_21, x_108, x_23, x_21, x_16);
x_110 = l_Lake_DSL_expandDepSpec___lambda__1___closed__49;
lean_inc(x_21);
lean_inc(x_12);
x_111 = l_Lean_Syntax_node4(x_12, x_110, x_66, x_109, x_98, x_21);
x_112 = l_Lake_DSL_expandDepSpec___lambda__1___closed__37;
lean_inc(x_12);
x_113 = l_Lean_Syntax_node5(x_12, x_112, x_50, x_57, x_64, x_111, x_21);
x_114 = l_Lake_DSL_expandDepSpec___lambda__1___closed__19;
x_115 = l_Lean_Syntax_node2(x_12, x_114, x_105, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_73);
x_117 = lean_ctor_get(x_74, 0);
lean_inc(x_117);
lean_dec(x_74);
x_118 = l_Lake_DSL_expandDepSpec___lambda__1___closed__82;
x_119 = l_String_intercalate(x_118, x_117);
x_120 = l_Lake_DSL_expandDepSpec___lambda__1___closed__83;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = l_Lean_Syntax_mkNameLit(x_121, x_55);
x_123 = l_Lake_DSL_expandDepSpec___lambda__1___closed__84;
x_124 = lean_array_push(x_123, x_122);
x_125 = l_Lake_DSL_expandDepSpec___lambda__1___closed__81;
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_55);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_124);
lean_inc(x_66);
lean_inc(x_12);
x_127 = l_Lean_Syntax_node3(x_12, x_90, x_72, x_66, x_126);
lean_inc(x_76);
lean_inc(x_12);
x_128 = l_Lean_Syntax_node5(x_12, x_19, x_127, x_76, x_91, x_76, x_100);
lean_inc_n(x_21, 2);
lean_inc(x_12);
x_129 = l_Lean_Syntax_node6(x_12, x_24, x_14, x_21, x_128, x_23, x_21, x_16);
x_130 = l_Lake_DSL_expandDepSpec___lambda__1___closed__49;
lean_inc(x_21);
lean_inc(x_12);
x_131 = l_Lean_Syntax_node4(x_12, x_130, x_66, x_129, x_98, x_21);
x_132 = l_Lake_DSL_expandDepSpec___lambda__1___closed__37;
lean_inc(x_12);
x_133 = l_Lean_Syntax_node5(x_12, x_132, x_50, x_57, x_64, x_131, x_21);
x_134 = l_Lake_DSL_expandDepSpec___lambda__1___closed__19;
x_135 = l_Lean_Syntax_node2(x_12, x_134, x_105, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_9);
return x_136;
}
}
}
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("none", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__3___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__3___closed__4;
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("some", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__3___closed__8;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_expandDepSpec___lambda__3___closed__4;
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___lambda__3___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = l_Lake_DSL_expandDepSpec___lambda__3___closed__3;
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Lake_DSL_expandDepSpec___lambda__3___closed__2;
x_18 = l_Lake_DSL_expandDepSpec___lambda__3___closed__7;
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lake_DSL_expandDepSpec___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_19, x_8, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_ctor_get(x_8, 5);
lean_inc(x_22);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
x_27 = l_Lake_DSL_expandDepSpec___lambda__3___closed__10;
x_28 = l_Lean_addMacroScope(x_26, x_27, x_25);
x_29 = l_Lake_DSL_expandDepSpec___lambda__3___closed__9;
x_30 = l_Lake_DSL_expandDepSpec___lambda__3___closed__13;
lean_inc(x_24);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
lean_inc(x_24);
x_33 = l_Lean_Syntax_node1(x_24, x_32, x_21);
x_34 = l_Lake_DSL_expandDepSpec___lambda__1___closed__63;
x_35 = l_Lean_Syntax_node2(x_24, x_34, x_31, x_33);
x_36 = l_Lake_DSL_expandDepSpec___lambda__2(x_1, x_2, x_3, x_7, x_4, x_5, x_35, x_8, x_9);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_9, 5);
lean_inc(x_11);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = l_Lake_DSL_expandDepSpec___lambda__3___closed__3;
x_17 = l_Lean_addMacroScope(x_15, x_16, x_14);
x_18 = l_Lake_DSL_expandDepSpec___lambda__3___closed__2;
x_19 = l_Lake_DSL_expandDepSpec___lambda__3___closed__7;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lake_DSL_expandDepSpec___lambda__3(x_1, x_2, x_3, x_4, x_8, x_5, x_20, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_9, 5);
lean_inc(x_23);
x_24 = 0;
x_25 = l_Lean_SourceInfo_fromRef(x_23, x_24);
lean_dec(x_23);
x_26 = lean_ctor_get(x_9, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
x_28 = l_Lake_DSL_expandDepSpec___lambda__3___closed__10;
x_29 = l_Lean_addMacroScope(x_27, x_28, x_26);
x_30 = l_Lake_DSL_expandDepSpec___lambda__3___closed__9;
x_31 = l_Lake_DSL_expandDepSpec___lambda__3___closed__13;
lean_inc(x_25);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Lake_DSL_expandDepSpec___lambda__1___closed__13;
lean_inc(x_25);
x_34 = l_Lean_Syntax_node1(x_25, x_33, x_22);
x_35 = l_Lake_DSL_expandDepSpec___lambda__1___closed__63;
x_36 = l_Lean_Syntax_node2(x_25, x_35, x_32, x_34);
x_37 = l_Lake_DSL_expandDepSpec___lambda__3(x_1, x_2, x_3, x_4, x_8, x_5, x_36, x_9, x_10);
return x_37;
}
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed require syntax", 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_16, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lake_DSL_expandDepSpec___lambda__4(x_2, x_3, x_4, x_5, x_8, x_6, x_21, x_20, x_9, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lake_DSL_expandDepSpec___lambda__4(x_2, x_3, x_4, x_5, x_8, x_6, x_24, x_23, x_9, x_10);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_2, x_16, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lake_DSL_expandDepSpec___lambda__5(x_2, x_3, x_4, x_5, x_6, x_8, x_21, x_20, x_9, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lake_DSL_expandDepSpec___lambda__5(x_2, x_3, x_4, x_5, x_6, x_8, x_24, x_23, x_9, x_10);
return x_25;
}
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Dependency", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_expandDepSpec___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_expandDepSpec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_expandDepSpec___closed__2;
x_3 = 0;
x_4 = l_Lean_mkCIdentFrom(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lake_DSL_depSpec___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_8 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_7, x_3, x_4);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lake_DSL_depSpec___closed__4;
lean_inc(x_10);
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
x_13 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_14 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_13, x_3, x_4);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lake_DSL_fromGit___closed__2;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lake_DSL_fromPath___closed__4;
lean_inc(x_16);
x_20 = l_Lean_Syntax_isOfKind(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_2);
x_21 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_22 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_21, x_3, x_4);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArg(x_16, x_9);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Syntax_isNone(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_25);
x_27 = l_Lean_Syntax_matchesNull(x_25, x_15);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_2);
x_28 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_29 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_28, x_3, x_4);
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Syntax_getArg(x_25, x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lake_DSL_expandDepSpec___closed__3;
x_34 = lean_box(0);
x_35 = l_Lake_DSL_expandDepSpec___lambda__1(x_10, x_33, x_23, x_2, x_34, x_32, x_3, x_4);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = l_Lake_DSL_expandDepSpec___closed__3;
x_38 = lean_box(0);
x_39 = l_Lake_DSL_expandDepSpec___lambda__1(x_10, x_37, x_23, x_2, x_38, x_36, x_3, x_4);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_16, x_40);
x_42 = l_Lean_Syntax_getArg(x_16, x_15);
x_43 = l_Lean_Syntax_isNone(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc(x_42);
x_44 = l_Lean_Syntax_matchesNull(x_42, x_15);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_2);
x_45 = l_Lake_DSL_expandDepSpec___lambda__5___closed__1;
x_46 = l_Lean_Macro_throwErrorAt___rarg(x_1, x_45, x_3, x_4);
lean_dec(x_1);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l_Lean_Syntax_getArg(x_42, x_40);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lake_DSL_expandDepSpec___closed__3;
x_50 = lean_box(0);
x_51 = l_Lake_DSL_expandDepSpec___lambda__6(x_16, x_1, x_10, x_49, x_41, x_2, x_50, x_48, x_3, x_4);
lean_dec(x_1);
lean_dec(x_16);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = l_Lake_DSL_expandDepSpec___closed__3;
x_54 = lean_box(0);
x_55 = l_Lake_DSL_expandDepSpec___lambda__6(x_16, x_1, x_10, x_53, x_41, x_2, x_54, x_52, x_3, x_4);
lean_dec(x_1);
lean_dec(x_16);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_expandDepSpec___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_DSL_expandDepSpec___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_DSL_expandDepSpec___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandDepSpec___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_DSL_expandDepSpec___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("requireDecl", 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromPath___closed__1;
x_2 = l_Lake_DSL_fromPath___closed__2;
x_3 = l_Lake_DSL_requireDecl___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_requireDecl___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_requireDecl___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_fromGit___closed__10;
x_2 = l_Lake_DSL_requireDecl___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("require ", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_requireDecl___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_requireDecl___closed__6;
x_3 = l_Lake_DSL_requireDecl___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_fromGit___closed__4;
x_2 = l_Lake_DSL_requireDecl___closed__9;
x_3 = l_Lake_DSL_depSpec;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_requireDecl___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lake_DSL_requireDecl___closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_requireDecl___closed__11;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL___aux__Lake__DSL__Require______macroRules__Lake__DSL__requireDecl__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_DSL_requireDecl___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_getOptional_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 5);
x_18 = l_Lean_replaceRef(x_11, x_17);
lean_dec(x_17);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_18);
x_19 = l_Lake_DSL_expandDepSpec(x_13, x_15, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_ctor_get(x_2, 4);
x_33 = lean_ctor_get(x_2, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_34 = l_Lean_replaceRef(x_11, x_33);
lean_dec(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_34);
x_36 = l_Lake_DSL_expandDepSpec(x_13, x_15, x_35, x_3);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_2, 5);
x_48 = l_Lean_replaceRef(x_11, x_47);
lean_dec(x_47);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_48);
x_49 = l_Lake_DSL_expandDepSpec(x_13, x_14, x_2, x_3);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_60 = lean_ctor_get(x_2, 2);
x_61 = lean_ctor_get(x_2, 3);
x_62 = lean_ctor_get(x_2, 4);
x_63 = lean_ctor_get(x_2, 5);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_64 = l_Lean_replaceRef(x_11, x_63);
lean_dec(x_63);
lean_dec(x_11);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
lean_ctor_set(x_65, 5, x_64);
x_66 = l_Lake_DSL_expandDepSpec(x_13, x_14, x_65, x_3);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_14, 0);
lean_inc(x_75);
lean_dec(x_14);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 5);
lean_inc(x_82);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_83 = x_2;
} else {
 lean_dec_ref(x_2);
 x_83 = lean_box(0);
}
x_84 = l_Lean_replaceRef(x_11, x_82);
lean_dec(x_82);
lean_dec(x_11);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set(x_85, 4, x_81);
lean_ctor_set(x_85, 5, x_84);
x_86 = l_Lake_DSL_expandDepSpec(x_13, x_76, x_85, x_3);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_instCoeRequireDeclCommand___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_DSL_instCoeRequireDeclCommand(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Require(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_fromPath___closed__1 = _init_l_Lake_DSL_fromPath___closed__1();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__1);
l_Lake_DSL_fromPath___closed__2 = _init_l_Lake_DSL_fromPath___closed__2();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__2);
l_Lake_DSL_fromPath___closed__3 = _init_l_Lake_DSL_fromPath___closed__3();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__3);
l_Lake_DSL_fromPath___closed__4 = _init_l_Lake_DSL_fromPath___closed__4();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__4);
l_Lake_DSL_fromPath___closed__5 = _init_l_Lake_DSL_fromPath___closed__5();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__5);
l_Lake_DSL_fromPath___closed__6 = _init_l_Lake_DSL_fromPath___closed__6();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__6);
l_Lake_DSL_fromPath___closed__7 = _init_l_Lake_DSL_fromPath___closed__7();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__7);
l_Lake_DSL_fromPath___closed__8 = _init_l_Lake_DSL_fromPath___closed__8();
lean_mark_persistent(l_Lake_DSL_fromPath___closed__8);
l_Lake_DSL_fromPath = _init_l_Lake_DSL_fromPath();
lean_mark_persistent(l_Lake_DSL_fromPath);
l_Lake_DSL_fromGit___closed__1 = _init_l_Lake_DSL_fromGit___closed__1();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__1);
l_Lake_DSL_fromGit___closed__2 = _init_l_Lake_DSL_fromGit___closed__2();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__2);
l_Lake_DSL_fromGit___closed__3 = _init_l_Lake_DSL_fromGit___closed__3();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__3);
l_Lake_DSL_fromGit___closed__4 = _init_l_Lake_DSL_fromGit___closed__4();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__4);
l_Lake_DSL_fromGit___closed__5 = _init_l_Lake_DSL_fromGit___closed__5();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__5);
l_Lake_DSL_fromGit___closed__6 = _init_l_Lake_DSL_fromGit___closed__6();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__6);
l_Lake_DSL_fromGit___closed__7 = _init_l_Lake_DSL_fromGit___closed__7();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__7);
l_Lake_DSL_fromGit___closed__8 = _init_l_Lake_DSL_fromGit___closed__8();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__8);
l_Lake_DSL_fromGit___closed__9 = _init_l_Lake_DSL_fromGit___closed__9();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__9);
l_Lake_DSL_fromGit___closed__10 = _init_l_Lake_DSL_fromGit___closed__10();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__10);
l_Lake_DSL_fromGit___closed__11 = _init_l_Lake_DSL_fromGit___closed__11();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__11);
l_Lake_DSL_fromGit___closed__12 = _init_l_Lake_DSL_fromGit___closed__12();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__12);
l_Lake_DSL_fromGit___closed__13 = _init_l_Lake_DSL_fromGit___closed__13();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__13);
l_Lake_DSL_fromGit___closed__14 = _init_l_Lake_DSL_fromGit___closed__14();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__14);
l_Lake_DSL_fromGit___closed__15 = _init_l_Lake_DSL_fromGit___closed__15();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__15);
l_Lake_DSL_fromGit___closed__16 = _init_l_Lake_DSL_fromGit___closed__16();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__16);
l_Lake_DSL_fromGit___closed__17 = _init_l_Lake_DSL_fromGit___closed__17();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__17);
l_Lake_DSL_fromGit___closed__18 = _init_l_Lake_DSL_fromGit___closed__18();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__18);
l_Lake_DSL_fromGit___closed__19 = _init_l_Lake_DSL_fromGit___closed__19();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__19);
l_Lake_DSL_fromGit___closed__20 = _init_l_Lake_DSL_fromGit___closed__20();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__20);
l_Lake_DSL_fromGit___closed__21 = _init_l_Lake_DSL_fromGit___closed__21();
lean_mark_persistent(l_Lake_DSL_fromGit___closed__21);
l_Lake_DSL_fromGit = _init_l_Lake_DSL_fromGit();
lean_mark_persistent(l_Lake_DSL_fromGit);
l_Lake_DSL_depSpec___closed__1 = _init_l_Lake_DSL_depSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__1);
l_Lake_DSL_depSpec___closed__2 = _init_l_Lake_DSL_depSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__2);
l_Lake_DSL_depSpec___closed__3 = _init_l_Lake_DSL_depSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__3);
l_Lake_DSL_depSpec___closed__4 = _init_l_Lake_DSL_depSpec___closed__4();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__4);
l_Lake_DSL_depSpec___closed__5 = _init_l_Lake_DSL_depSpec___closed__5();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__5);
l_Lake_DSL_depSpec___closed__6 = _init_l_Lake_DSL_depSpec___closed__6();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__6);
l_Lake_DSL_depSpec___closed__7 = _init_l_Lake_DSL_depSpec___closed__7();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__7);
l_Lake_DSL_depSpec___closed__8 = _init_l_Lake_DSL_depSpec___closed__8();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__8);
l_Lake_DSL_depSpec___closed__9 = _init_l_Lake_DSL_depSpec___closed__9();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__9);
l_Lake_DSL_depSpec___closed__10 = _init_l_Lake_DSL_depSpec___closed__10();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__10);
l_Lake_DSL_depSpec___closed__11 = _init_l_Lake_DSL_depSpec___closed__11();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__11);
l_Lake_DSL_depSpec___closed__12 = _init_l_Lake_DSL_depSpec___closed__12();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__12);
l_Lake_DSL_depSpec___closed__13 = _init_l_Lake_DSL_depSpec___closed__13();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__13);
l_Lake_DSL_depSpec___closed__14 = _init_l_Lake_DSL_depSpec___closed__14();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__14);
l_Lake_DSL_depSpec___closed__15 = _init_l_Lake_DSL_depSpec___closed__15();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__15);
l_Lake_DSL_depSpec___closed__16 = _init_l_Lake_DSL_depSpec___closed__16();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__16);
l_Lake_DSL_depSpec___closed__17 = _init_l_Lake_DSL_depSpec___closed__17();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__17);
l_Lake_DSL_depSpec___closed__18 = _init_l_Lake_DSL_depSpec___closed__18();
lean_mark_persistent(l_Lake_DSL_depSpec___closed__18);
l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
lean_mark_persistent(l_Lake_DSL_depSpec);
l_Lake_DSL_expandDepSpec___lambda__1___closed__1 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__1);
l_Lake_DSL_expandDepSpec___lambda__1___closed__2 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__2();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__2);
l_Lake_DSL_expandDepSpec___lambda__1___closed__3 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__3();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__3);
l_Lake_DSL_expandDepSpec___lambda__1___closed__4 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__4();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__4);
l_Lake_DSL_expandDepSpec___lambda__1___closed__5 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__5();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__5);
l_Lake_DSL_expandDepSpec___lambda__1___closed__6 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__6();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__6);
l_Lake_DSL_expandDepSpec___lambda__1___closed__7 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__7();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__7);
l_Lake_DSL_expandDepSpec___lambda__1___closed__8 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__8();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__8);
l_Lake_DSL_expandDepSpec___lambda__1___closed__9 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__9();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__9);
l_Lake_DSL_expandDepSpec___lambda__1___closed__10 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__10();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__10);
l_Lake_DSL_expandDepSpec___lambda__1___closed__11 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__11();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__11);
l_Lake_DSL_expandDepSpec___lambda__1___closed__12 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__12();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__12);
l_Lake_DSL_expandDepSpec___lambda__1___closed__13 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__13();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__13);
l_Lake_DSL_expandDepSpec___lambda__1___closed__14 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__14();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__14);
l_Lake_DSL_expandDepSpec___lambda__1___closed__15 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__15();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__15);
l_Lake_DSL_expandDepSpec___lambda__1___closed__16 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__16();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__16);
l_Lake_DSL_expandDepSpec___lambda__1___closed__17 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__17();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__17);
l_Lake_DSL_expandDepSpec___lambda__1___closed__18 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__18();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__18);
l_Lake_DSL_expandDepSpec___lambda__1___closed__19 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__19();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__19);
l_Lake_DSL_expandDepSpec___lambda__1___closed__20 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__20();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__20);
l_Lake_DSL_expandDepSpec___lambda__1___closed__21 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__21();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__21);
l_Lake_DSL_expandDepSpec___lambda__1___closed__22 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__22();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__22);
l_Lake_DSL_expandDepSpec___lambda__1___closed__23 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__23();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__23);
l_Lake_DSL_expandDepSpec___lambda__1___closed__24 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__24();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__24);
l_Lake_DSL_expandDepSpec___lambda__1___closed__25 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__25();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__25);
l_Lake_DSL_expandDepSpec___lambda__1___closed__26 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__26();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__26);
l_Lake_DSL_expandDepSpec___lambda__1___closed__27 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__27();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__27);
l_Lake_DSL_expandDepSpec___lambda__1___closed__28 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__28();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__28);
l_Lake_DSL_expandDepSpec___lambda__1___closed__29 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__29();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__29);
l_Lake_DSL_expandDepSpec___lambda__1___closed__30 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__30();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__30);
l_Lake_DSL_expandDepSpec___lambda__1___closed__31 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__31();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__31);
l_Lake_DSL_expandDepSpec___lambda__1___closed__32 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__32();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__32);
l_Lake_DSL_expandDepSpec___lambda__1___closed__33 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__33();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__33);
l_Lake_DSL_expandDepSpec___lambda__1___closed__34 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__34();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__34);
l_Lake_DSL_expandDepSpec___lambda__1___closed__35 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__35();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__35);
l_Lake_DSL_expandDepSpec___lambda__1___closed__36 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__36();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__36);
l_Lake_DSL_expandDepSpec___lambda__1___closed__37 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__37();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__37);
l_Lake_DSL_expandDepSpec___lambda__1___closed__38 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__38();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__38);
l_Lake_DSL_expandDepSpec___lambda__1___closed__39 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__39();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__39);
l_Lake_DSL_expandDepSpec___lambda__1___closed__40 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__40();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__40);
l_Lake_DSL_expandDepSpec___lambda__1___closed__41 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__41();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__41);
l_Lake_DSL_expandDepSpec___lambda__1___closed__42 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__42();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__42);
l_Lake_DSL_expandDepSpec___lambda__1___closed__43 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__43();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__43);
l_Lake_DSL_expandDepSpec___lambda__1___closed__44 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__44();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__44);
l_Lake_DSL_expandDepSpec___lambda__1___closed__45 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__45();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__45);
l_Lake_DSL_expandDepSpec___lambda__1___closed__46 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__46();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__46);
l_Lake_DSL_expandDepSpec___lambda__1___closed__47 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__47();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__47);
l_Lake_DSL_expandDepSpec___lambda__1___closed__48 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__48();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__48);
l_Lake_DSL_expandDepSpec___lambda__1___closed__49 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__49();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__49);
l_Lake_DSL_expandDepSpec___lambda__1___closed__50 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__50();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__50);
l_Lake_DSL_expandDepSpec___lambda__1___closed__51 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__51();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__51);
l_Lake_DSL_expandDepSpec___lambda__1___closed__52 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__52();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__52);
l_Lake_DSL_expandDepSpec___lambda__1___closed__53 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__53();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__53);
l_Lake_DSL_expandDepSpec___lambda__1___closed__54 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__54();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__54);
l_Lake_DSL_expandDepSpec___lambda__1___closed__55 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__55();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__55);
l_Lake_DSL_expandDepSpec___lambda__1___closed__56 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__56();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__56);
l_Lake_DSL_expandDepSpec___lambda__1___closed__57 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__57();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__57);
l_Lake_DSL_expandDepSpec___lambda__1___closed__58 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__58();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__58);
l_Lake_DSL_expandDepSpec___lambda__1___closed__59 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__59();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__59);
l_Lake_DSL_expandDepSpec___lambda__1___closed__60 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__60();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__60);
l_Lake_DSL_expandDepSpec___lambda__1___closed__61 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__61();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__61);
l_Lake_DSL_expandDepSpec___lambda__1___closed__62 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__62();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__62);
l_Lake_DSL_expandDepSpec___lambda__1___closed__63 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__63();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__63);
l_Lake_DSL_expandDepSpec___lambda__1___closed__64 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__64();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__64);
l_Lake_DSL_expandDepSpec___lambda__1___closed__65 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__65();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__65);
l_Lake_DSL_expandDepSpec___lambda__1___closed__66 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__66();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__66);
l_Lake_DSL_expandDepSpec___lambda__1___closed__67 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__67();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__67);
l_Lake_DSL_expandDepSpec___lambda__1___closed__68 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__68();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__68);
l_Lake_DSL_expandDepSpec___lambda__1___closed__69 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__69();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__69);
l_Lake_DSL_expandDepSpec___lambda__1___closed__70 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__70();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__70);
l_Lake_DSL_expandDepSpec___lambda__1___closed__71 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__71();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__71);
l_Lake_DSL_expandDepSpec___lambda__1___closed__72 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__72();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__72);
l_Lake_DSL_expandDepSpec___lambda__1___closed__73 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__73();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__73);
l_Lake_DSL_expandDepSpec___lambda__1___closed__74 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__74();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__74);
l_Lake_DSL_expandDepSpec___lambda__1___closed__75 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__75();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__75);
l_Lake_DSL_expandDepSpec___lambda__1___closed__76 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__76();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__76);
l_Lake_DSL_expandDepSpec___lambda__1___closed__77 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__77();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__77);
l_Lake_DSL_expandDepSpec___lambda__1___closed__78 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__78();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__78);
l_Lake_DSL_expandDepSpec___lambda__1___closed__79 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__79();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__79);
l_Lake_DSL_expandDepSpec___lambda__1___closed__80 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__80();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__80);
l_Lake_DSL_expandDepSpec___lambda__1___closed__81 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__81();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__81);
l_Lake_DSL_expandDepSpec___lambda__1___closed__82 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__82();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__82);
l_Lake_DSL_expandDepSpec___lambda__1___closed__83 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__83();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__83);
l_Lake_DSL_expandDepSpec___lambda__1___closed__84 = _init_l_Lake_DSL_expandDepSpec___lambda__1___closed__84();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__1___closed__84);
l_Lake_DSL_expandDepSpec___lambda__2___closed__1 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__1);
l_Lake_DSL_expandDepSpec___lambda__2___closed__2 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__2();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__2);
l_Lake_DSL_expandDepSpec___lambda__2___closed__3 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__3();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__3);
l_Lake_DSL_expandDepSpec___lambda__2___closed__4 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__4();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__4);
l_Lake_DSL_expandDepSpec___lambda__2___closed__5 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__5();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__5);
l_Lake_DSL_expandDepSpec___lambda__2___closed__6 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__6();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__6);
l_Lake_DSL_expandDepSpec___lambda__2___closed__7 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__7();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__7);
l_Lake_DSL_expandDepSpec___lambda__2___closed__8 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__8();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__8);
l_Lake_DSL_expandDepSpec___lambda__2___closed__9 = _init_l_Lake_DSL_expandDepSpec___lambda__2___closed__9();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__2___closed__9);
l_Lake_DSL_expandDepSpec___lambda__3___closed__1 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__1);
l_Lake_DSL_expandDepSpec___lambda__3___closed__2 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__2();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__2);
l_Lake_DSL_expandDepSpec___lambda__3___closed__3 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__3();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__3);
l_Lake_DSL_expandDepSpec___lambda__3___closed__4 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__4();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__4);
l_Lake_DSL_expandDepSpec___lambda__3___closed__5 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__5();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__5);
l_Lake_DSL_expandDepSpec___lambda__3___closed__6 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__6();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__6);
l_Lake_DSL_expandDepSpec___lambda__3___closed__7 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__7();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__7);
l_Lake_DSL_expandDepSpec___lambda__3___closed__8 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__8();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__8);
l_Lake_DSL_expandDepSpec___lambda__3___closed__9 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__9();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__9);
l_Lake_DSL_expandDepSpec___lambda__3___closed__10 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__10();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__10);
l_Lake_DSL_expandDepSpec___lambda__3___closed__11 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__11();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__11);
l_Lake_DSL_expandDepSpec___lambda__3___closed__12 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__12();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__12);
l_Lake_DSL_expandDepSpec___lambda__3___closed__13 = _init_l_Lake_DSL_expandDepSpec___lambda__3___closed__13();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__3___closed__13);
l_Lake_DSL_expandDepSpec___lambda__5___closed__1 = _init_l_Lake_DSL_expandDepSpec___lambda__5___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___lambda__5___closed__1);
l_Lake_DSL_expandDepSpec___closed__1 = _init_l_Lake_DSL_expandDepSpec___closed__1();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___closed__1);
l_Lake_DSL_expandDepSpec___closed__2 = _init_l_Lake_DSL_expandDepSpec___closed__2();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___closed__2);
l_Lake_DSL_expandDepSpec___closed__3 = _init_l_Lake_DSL_expandDepSpec___closed__3();
lean_mark_persistent(l_Lake_DSL_expandDepSpec___closed__3);
l_Lake_DSL_requireDecl___closed__1 = _init_l_Lake_DSL_requireDecl___closed__1();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__1);
l_Lake_DSL_requireDecl___closed__2 = _init_l_Lake_DSL_requireDecl___closed__2();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__2);
l_Lake_DSL_requireDecl___closed__3 = _init_l_Lake_DSL_requireDecl___closed__3();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__3);
l_Lake_DSL_requireDecl___closed__4 = _init_l_Lake_DSL_requireDecl___closed__4();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__4);
l_Lake_DSL_requireDecl___closed__5 = _init_l_Lake_DSL_requireDecl___closed__5();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__5);
l_Lake_DSL_requireDecl___closed__6 = _init_l_Lake_DSL_requireDecl___closed__6();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__6);
l_Lake_DSL_requireDecl___closed__7 = _init_l_Lake_DSL_requireDecl___closed__7();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__7);
l_Lake_DSL_requireDecl___closed__8 = _init_l_Lake_DSL_requireDecl___closed__8();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__8);
l_Lake_DSL_requireDecl___closed__9 = _init_l_Lake_DSL_requireDecl___closed__9();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__9);
l_Lake_DSL_requireDecl___closed__10 = _init_l_Lake_DSL_requireDecl___closed__10();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__10);
l_Lake_DSL_requireDecl___closed__11 = _init_l_Lake_DSL_requireDecl___closed__11();
lean_mark_persistent(l_Lake_DSL_requireDecl___closed__11);
l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
lean_mark_persistent(l_Lake_DSL_requireDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
