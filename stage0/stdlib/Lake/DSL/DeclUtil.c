// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: Lake.DSL.Config Lake.Util.Binder Lake.Util.Name Lean.Parser.Command Lean.Elab.Command
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
static lean_object* l_Lake_DSL_declField___closed__8;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7;
static lean_object* l_Lake_DSL_optConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_simpleDeclSig;
static lean_object* l_Lake_DSL_declValWhere___closed__7;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__13;
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__5;
static lean_object* l_Lake_DSL_simpleBinder___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_declValStruct;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__8;
static lean_object* l_Lake_DSL_declValDo___closed__8;
static lean_object* l_Lake_DSL_identOrStr___closed__9;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__4;
static lean_object* l_Lake_DSL_expandAttrs___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
static lean_object* l_Lake_DSL_elabConfig___closed__2;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__1;
static lean_object* l_Lake_DSL_simpleBinder___closed__4;
lean_object* l_Lean_TSyntax_getString(lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__12;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__1;
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_simpleBinder;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_optConfig;
static lean_object* l_Lake_DSL_optConfig___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__1;
static lean_object* l_Lake_DSL_structVal___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_identOrStr;
lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__9;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_DSL_structVal___closed__2;
static lean_object* l_Lake_DSL_expandAttrs___closed__5;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__12;
static lean_object* l_Lake_DSL_expandAttrs___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__7;
static lean_object* l_Lake_DSL_declValStruct___closed__5;
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__9;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__11;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__4;
static lean_object* l_Lake_DSL_expandAttrs___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_bracketedSimpleBinder;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_declValWhere;
static lean_object* l_Lake_DSL_identOrStr___closed__8;
static lean_object* l_Lake_DSL_declValStruct___closed__1;
static lean_object* l_Lake_DSL_declValDo___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__13;
static lean_object* l_Lake_DSL_declValWhere___closed__4;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfig___closed__6;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__13;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11;
static lean_object* l_Lake_DSL_identOrStr___closed__12;
static lean_object* l_Lake_DSL_identOrStr___closed__6;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleBinder___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__7;
static lean_object* l_Lake_DSL_packageDeclName___closed__2;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__6;
static lean_object* l_Lake_DSL_declValDo___closed__17;
static lean_object* l_Lake_DSL_simpleBinder___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__3;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__6;
static lean_object* l_Lake_DSL_declValDo___closed__14;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__15;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__11;
static lean_object* l_Lake_DSL_elabConfig___closed__4;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
static lean_object* l_Lake_DSL_elabConfig___closed__5;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_packageDeclName;
static lean_object* l_Lake_DSL_identOrStr___closed__11;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__11;
static lean_object* l_Lake_DSL_declValDo___closed__1;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__9;
static lean_object* l_Lake_DSL_elabConfig___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
static lean_object* l_Lake_DSL_declValDo___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_structVal;
static lean_object* l_Lake_DSL_structVal___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__8;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_DSL_declValDo;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__2;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11;
static lean_object* l_Lake_DSL_declField___closed__12;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__2;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__13;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__7;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8;
static lean_object* l_Lake_DSL_elabConfig___closed__3;
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__4;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__8;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__6;
static lean_object* l_Lake_DSL_declField___closed__5;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__7;
static lean_object* l_Lake_DSL_declValDo___closed__6;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
static lean_object* l_Lake_DSL_identOrStr___closed__14;
static lean_object* l_Lake_DSL_declValDo___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__12;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__14;
static lean_object* l_Lake_DSL_structVal___closed__12;
static lean_object* l_Lake_DSL_declField___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_declField;
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__1;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1;
static lean_object* l_Lake_DSL_elabConfig___closed__1;
static lean_object* l_Lake_DSL_declValStruct___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__7;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__5;
static lean_object* l_Lake_DSL_optConfig___closed__2;
static lean_object* l_Lake_DSL_declValWhere___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__7;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_DSL_declField___closed__1;
static lean_object* l_Lake_DSL_expandAttrs___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_DSL_structVal___closed__14;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__10;
static lean_object* l_Lake_DSL_identOrStr___closed__4;
static lean_object* l_Lake_DSL_mkConfigFields___closed__1;
static lean_object* l_Lake_DSL_declField___closed__6;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_DSL_declValDo___closed__5;
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__8;
static lean_object* l_Lake_DSL_optConfig___closed__5;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2;
static lean_object* l_Lake_DSL_mkConfigFields___closed__2;
static lean_object* l_Lake_DSL_declValDo___closed__11;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1;
static lean_object* l_Lake_DSL_declField___closed__3;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__2;
static lean_object* l_Lake_DSL_structVal___closed__1;
static lean_object* l_Lake_DSL_identOrStr___closed__2;
static lean_object* l_Lake_DSL_packageDeclName___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__10;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4;
static lean_object* l_Lake_DSL_declValWhere___closed__5;
static lean_object* l_Lake_DSL_optConfig___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__10;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__3;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__5;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__4;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9;
static lean_object* l_Lake_DSL_declValDo___closed__16;
static lean_object* l_Lake_DSL_declValDo___closed__13;
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__10;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__14;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__16;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7;
static lean_object* _init_l_Lake_DSL_packageDeclName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_package", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_packageDeclName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_packageDeclName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_packageDeclName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_packageDeclName___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandAttrs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attributes", 10, 10);
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
static lean_object* _init_l_Lake_DSL_identOrStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DSL", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identOrStr", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_identOrStr___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_identOrStr___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_identOrStr___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_identOrStr___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_identOrStr___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_identOrStr___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__6;
x_2 = l_Lake_DSL_identOrStr___closed__9;
x_3 = l_Lake_DSL_identOrStr___closed__12;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__3;
x_2 = l_Lake_DSL_identOrStr___closed__4;
x_3 = l_Lake_DSL_identOrStr___closed__13;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_identOrStr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_identOrStr___closed__14;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_DSL_identOrStr___closed__4;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lake_DSL_identOrStr___closed__8;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_DSL_identOrStr___closed__11;
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Lean_TSyntax_getString(x_6);
x_13 = lean_box(0);
x_14 = l_Lean_Name_str___override(x_13, x_12);
x_15 = 0;
x_16 = l_Lean_mkIdentFrom(x_6, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
else
{
return x_6;
}
}
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declField", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_declField___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declField___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_identOrStr___closed__9;
x_3 = l_Lake_DSL_declField___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declField___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_declField___closed__7;
x_3 = l_Lake_DSL_declField___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declField___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__1;
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = l_Lake_DSL_declField___closed__11;
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
x_1 = l_Lake_DSL_declField___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structVal", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_structVal___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
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
x_1 = lean_mk_string_unchecked("structInstFields", 16, 16);
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
x_1 = lean_mk_string_unchecked("sepByIndentSemicolon", 20, 20);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__8;
x_2 = l_Lake_DSL_declField;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structVal___closed__6;
x_2 = l_Lake_DSL_structVal___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_structVal___closed__4;
x_3 = l_Lake_DSL_structVal___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_structVal___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_structVal___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_structVal___closed__11;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structVal___closed__1;
x_2 = l_Lake_DSL_structVal___closed__2;
x_3 = l_Lake_DSL_structVal___closed__14;
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
x_1 = l_Lake_DSL_structVal___closed__15;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declValDo", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_declValDo___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppSpace", 7, 7);
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
x_1 = lean_mk_string_unchecked("do", 2, 2);
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
x_1 = l_Lake_DSL_declField___closed__4;
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
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declValDo___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whereDecls", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_declValDo___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_declValDo___closed__13;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declValDo___closed__11;
x_2 = l_Lake_DSL_declValDo___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_declValDo___closed__9;
x_3 = l_Lake_DSL_declValDo___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValDo___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValDo___closed__1;
x_2 = l_Lake_DSL_declValDo___closed__2;
x_3 = l_Lake_DSL_declValDo___closed__16;
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
x_1 = l_Lake_DSL_declValDo___closed__17;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declValStruct", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_declValStruct___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValStruct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
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
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_declValStruct___closed__3;
x_3 = l_Lake_DSL_declValDo___closed__15;
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
x_1 = lean_mk_string_unchecked("declValWhere", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_declValWhere___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where ", 7, 7);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_declValWhere___closed__4;
x_3 = l_Lake_DSL_structVal___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_declValWhere___closed__5;
x_3 = l_Lake_DSL_declValDo___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_declValWhere___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declValWhere___closed__1;
x_2 = l_Lake_DSL_declValWhere___closed__2;
x_3 = l_Lake_DSL_declValWhere___closed__6;
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
x_1 = l_Lake_DSL_declValWhere___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpleDeclSig", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_simpleDeclSig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeSpec", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_simpleDeclSig___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_simpleDeclSig___closed__4;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_identOrStr___closed__9;
x_3 = l_Lake_DSL_simpleDeclSig___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declValSimple", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_simpleDeclSig___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_simpleDeclSig___closed__9;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_simpleDeclSig___closed__6;
x_3 = l_Lake_DSL_simpleDeclSig___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleDeclSig___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_simpleDeclSig___closed__1;
x_2 = l_Lake_DSL_simpleDeclSig___closed__2;
x_3 = l_Lake_DSL_simpleDeclSig___closed__11;
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
x_1 = l_Lake_DSL_simpleDeclSig___closed__12;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_optConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_optConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_optConfig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_optConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__6;
x_2 = l_Lake_DSL_declValWhere;
x_3 = l_Lake_DSL_declValStruct;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_optConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declValDo___closed__11;
x_2 = l_Lake_DSL_optConfig___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_optConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_optConfig___closed__1;
x_2 = l_Lake_DSL_optConfig___closed__2;
x_3 = l_Lake_DSL_optConfig___closed__4;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_optConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_DSL_optConfig___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bracketedSimpleBinder", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_bracketedSimpleBinder___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_bracketedSimpleBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
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
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__4;
x_3 = l_Lake_DSL_identOrStr___closed__9;
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
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
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
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_bracketedSimpleBinder___closed__7;
x_3 = l_Lake_DSL_declField___closed__10;
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
x_1 = l_Lake_DSL_declValDo___closed__11;
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
x_1 = l_Lake_DSL_declField___closed__4;
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
x_1 = lean_mk_string_unchecked(")", 1, 1);
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
x_1 = l_Lake_DSL_declField___closed__4;
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
x_1 = lean_mk_string_unchecked("simpleBinder", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_simpleBinder___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_simpleBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__6;
x_2 = l_Lake_DSL_identOrStr___closed__9;
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
x_1 = lean_mk_string_unchecked("hole", 4, 4);
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
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
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
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
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
x_26 = l_Lake_DSL_identOrStr___closed__8;
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
x_72 = l_Lake_DSL_identOrStr___closed__8;
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
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL_expandOptSimpleBinder(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_12, x_8, x_2, x_3, x_13);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_20, x_8, x_2, x_3, x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_25;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_9);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_21);
x_23 = l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2(x_2, x_22, x_4, x_8);
return x_23;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed field declaration syntax", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' field '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_6, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; 
x_13 = lean_array_uget(x_4, x_6);
x_21 = l_Lake_DSL_declField___closed__2;
lean_inc(x_13);
x_22 = l_Lean_Syntax_isOfKind(x_13, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_1);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2;
x_24 = l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1(x_13, x_23, x_8, x_9, x_10);
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Syntax_getArg(x_13, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_13, x_31);
x_33 = l_Lean_Syntax_getId(x_30);
lean_inc(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8;
lean_inc(x_1);
x_36 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_1);
x_37 = l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(x_36, x_8, x_9, x_10);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_st_ref_get(x_9, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_1);
x_46 = l_Lean_findField_x3f(x_45, x_1, x_33);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_32);
x_47 = 0;
lean_inc(x_1);
x_48 = l_Lean_MessageData_ofConstName(x_1, x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_41, 0, x_49);
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_50);
lean_ctor_set(x_37, 0, x_41);
x_51 = l_Lean_MessageData_ofName(x_33);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = 1;
lean_inc(x_8);
x_56 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_30, x_54, x_55, x_47, x_8, x_9, x_44);
lean_dec(x_30);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_7);
x_14 = x_58;
x_15 = x_57;
goto block_20;
}
else
{
uint8_t x_59; 
lean_free_object(x_37);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_46, 0);
lean_dec(x_60);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 0, x_30);
x_61 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_33, x_41);
lean_ctor_set(x_46, 0, x_61);
x_14 = x_46;
x_15 = x_44;
goto block_20;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_46);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 0, x_30);
x_62 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_33, x_41);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_14 = x_63;
x_15 = x_44;
goto block_20;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_1);
x_67 = l_Lean_findField_x3f(x_66, x_1, x_33);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_32);
x_68 = 0;
lean_inc(x_1);
x_69 = l_Lean_MessageData_ofConstName(x_1, x_68);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_72);
lean_ctor_set(x_37, 0, x_71);
x_73 = l_Lean_MessageData_ofName(x_33);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_37);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = 1;
lean_inc(x_8);
x_78 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_30, x_76, x_77, x_68, x_8, x_9, x_65);
lean_dec(x_30);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_7);
x_14 = x_80;
x_15 = x_79;
goto block_20;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_37);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_30);
lean_ctor_set(x_82, 1, x_32);
x_83 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_33, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
x_14 = x_84;
x_15 = x_65;
goto block_20;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_37, 1);
lean_inc(x_85);
lean_dec(x_37);
x_86 = lean_st_ref_get(x_9, x_85);
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
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_1);
x_91 = l_Lean_findField_x3f(x_90, x_1, x_33);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_32);
x_92 = 0;
lean_inc(x_1);
x_93 = l_Lean_MessageData_ofConstName(x_1, x_92);
x_94 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(7, 2, 0);
} else {
 x_95 = x_89;
 lean_ctor_set_tag(x_95, 7);
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_MessageData_ofName(x_33);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = 1;
lean_inc(x_8);
x_103 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_30, x_101, x_102, x_92, x_8, x_9, x_88);
lean_dec(x_30);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_7);
x_14 = x_105;
x_15 = x_104;
goto block_20;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_106 = x_91;
} else {
 lean_dec_ref(x_91);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_89;
}
lean_ctor_set(x_107, 0, x_30);
lean_ctor_set(x_107, 1, x_32);
x_108 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_33, x_107);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
x_14 = x_109;
x_15 = x_88;
goto block_20;
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_6 = x_18;
x_7 = x_16;
x_10 = x_15;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_SourceInfo_fromRef(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstField", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstLVal", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1;
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_3 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1;
x_2 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(x_1, x_7, x_3, x_4, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 1;
x_17 = l_Lean_mkIdentFrom(x_14, x_8, x_16);
lean_dec(x_14);
x_18 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1;
x_19 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5;
x_20 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7;
x_21 = l_Lean_Syntax_node2(x_18, x_19, x_17, x_20);
x_22 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9;
x_23 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11;
x_24 = l_Lean_Syntax_node2(x_18, x_22, x_23, x_15);
x_25 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_26 = l_Lean_Syntax_node3(x_18, x_25, x_20, x_20, x_24);
x_27 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3;
x_28 = l_Lean_Syntax_node2(x_18, x_27, x_21, x_26);
x_29 = lean_array_push(x_12, x_28);
x_1 = x_29;
x_2 = x_10;
x_5 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lake_DSL_mkConfigFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lake_DSL_structVal___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_mkConfigFields___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_3 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_array_size(x_2);
x_9 = 0;
lean_inc(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(x_1, x_2, x_7, x_2, x_8, x_9, x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lake_DSL_expandAttrs___closed__1;
x_15 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(x_14, x_11, x_3, x_4, x_12);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lake_DSL_mkConfigFields___closed__2;
x_19 = l_Lean_Syntax_mkSep(x_17, x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
x_21 = lean_array_mk(x_20);
x_22 = lean_box(2);
x_23 = l_Lake_DSL_mkConfigFields___closed__1;
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = l_Lake_DSL_mkConfigFields___closed__2;
x_28 = l_Lean_Syntax_mkSep(x_25, x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
x_30 = lean_array_mk(x_29);
x_31 = lean_box(2);
x_32 = l_Lake_DSL_mkConfigFields___closed__1;
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lake_DSL_mkConfigFields___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DSL_mkConfigFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_addMacroScope(x_6, x_1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_addMacroScope(x_6, x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1___boxed), 4, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkIdentFrom(x_1, x_8, x_2);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Lean_mkIdentFrom(x_1, x_10, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 0;
x_9 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1(x_6, x_8, x_2, x_3, x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_DSL_expandIdentOrStrAsIdent(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_mkConfigDeclIdent___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("where", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whereStructInst", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declModifiers", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__13() {
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
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_elabConfig___lambda__1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optDeclSig", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfig___lambda__1___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Syntax_getArgs(x_1);
x_13 = l_Lean_Syntax_getHeadInfo(x_2);
x_14 = l_Lean_Syntax_TSepArray_getElems___rarg(x_12);
lean_dec(x_12);
x_15 = l_Lake_DSL_elabConfig___lambda__1___closed__1;
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_9);
x_17 = l_Lake_DSL_mkConfigFields(x_3, x_14, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_getRef(x_9, x_10, x_19);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_164; 
x_164 = lean_box(0);
x_22 = x_164;
goto block_163;
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_8);
if (x_165 == 0)
{
x_22 = x_8;
goto block_163;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_8, 0);
lean_inc(x_166);
lean_dec(x_8);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_22 = x_167;
goto block_163;
}
}
block_163:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = l_Lean_mkOptionalNode(x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_mk(x_28);
x_30 = lean_box(2);
x_31 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = 0;
x_34 = l_Lean_SourceInfo_fromRef(x_24, x_33);
lean_dec(x_24);
x_35 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_25);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_44 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_34);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_45, 6);
lean_inc(x_34);
x_47 = l_Lean_Syntax_node6(x_34, x_46, x_45, x_45, x_45, x_45, x_45, x_45);
x_48 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_34);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_48);
lean_ctor_set(x_39, 0, x_34);
x_49 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_49);
lean_ctor_set(x_35, 0, x_4);
x_50 = lean_array_mk(x_35);
x_51 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_30);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
x_53 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_34);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_34);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_34);
x_56 = l_Lean_Syntax_node2(x_34, x_55, x_54, x_5);
lean_inc(x_34);
x_57 = l_Lean_Syntax_node1(x_34, x_43, x_56);
x_58 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_45);
lean_inc(x_34);
x_59 = l_Lean_Syntax_node2(x_34, x_58, x_45, x_57);
x_60 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_34);
x_61 = l_Lean_Syntax_node5(x_34, x_60, x_39, x_52, x_59, x_32, x_45);
x_62 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_63 = l_Lean_Syntax_node2(x_34, x_62, x_47, x_61);
lean_inc(x_63);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_63, x_64, x_9, x_10, x_41);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_dec(x_39);
x_67 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_68 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_34);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_34);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_68);
x_70 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_69, 6);
lean_inc(x_34);
x_71 = l_Lean_Syntax_node6(x_34, x_70, x_69, x_69, x_69, x_69, x_69, x_69);
x_72 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_34);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_34);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_74);
lean_ctor_set(x_35, 0, x_4);
x_75 = lean_array_mk(x_35);
x_76 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_30);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
x_78 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_34);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_34);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_34);
x_81 = l_Lean_Syntax_node2(x_34, x_80, x_79, x_5);
lean_inc(x_34);
x_82 = l_Lean_Syntax_node1(x_34, x_67, x_81);
x_83 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_69);
lean_inc(x_34);
x_84 = l_Lean_Syntax_node2(x_34, x_83, x_69, x_82);
x_85 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_34);
x_86 = l_Lean_Syntax_node5(x_34, x_85, x_73, x_77, x_84, x_32, x_69);
x_87 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_88 = l_Lean_Syntax_node2(x_34, x_87, x_71, x_86);
lean_inc(x_88);
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_89, 0, x_88);
x_90 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_88, x_89, x_9, x_10, x_66);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_91 = lean_ctor_get(x_35, 1);
lean_inc(x_91);
lean_dec(x_35);
x_92 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_91);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_96 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_34);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_34);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
x_98 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_97, 6);
lean_inc(x_34);
x_99 = l_Lean_Syntax_node6(x_34, x_98, x_97, x_97, x_97, x_97, x_97, x_97);
x_100 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_34);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(2, 2, 0);
} else {
 x_101 = x_94;
 lean_ctor_set_tag(x_101, 2);
}
lean_ctor_set(x_101, 0, x_34);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_4);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_mk(x_103);
x_105 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_30);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
x_107 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_34);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_34);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_34);
x_110 = l_Lean_Syntax_node2(x_34, x_109, x_108, x_5);
lean_inc(x_34);
x_111 = l_Lean_Syntax_node1(x_34, x_95, x_110);
x_112 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_97);
lean_inc(x_34);
x_113 = l_Lean_Syntax_node2(x_34, x_112, x_97, x_111);
x_114 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_34);
x_115 = l_Lean_Syntax_node5(x_34, x_114, x_101, x_106, x_113, x_32, x_97);
x_116 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_117 = l_Lean_Syntax_node2(x_34, x_116, x_99, x_115);
lean_inc(x_117);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_118, 0, x_117);
x_119 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_117, x_118, x_9, x_10, x_93);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_120 = lean_ctor_get(x_21, 0);
x_121 = lean_ctor_get(x_21, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_21);
x_122 = l_Lean_mkOptionalNode(x_22);
lean_dec(x_22);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_20);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_18);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_16);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_mk(x_125);
x_127 = lean_box(2);
x_128 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_126);
x_130 = 0;
x_131 = l_Lean_SourceInfo_fromRef(x_120, x_130);
lean_dec(x_120);
x_132 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_121);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_133);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_139 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_131);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_139);
x_141 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_140, 6);
lean_inc(x_131);
x_142 = l_Lean_Syntax_node6(x_131, x_141, x_140, x_140, x_140, x_140, x_140, x_140);
x_143 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_131);
if (lean_is_scalar(x_137)) {
 x_144 = lean_alloc_ctor(2, 2, 0);
} else {
 x_144 = x_137;
 lean_ctor_set_tag(x_144, 2);
}
lean_ctor_set(x_144, 0, x_131);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
if (lean_is_scalar(x_134)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_134;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_4);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_array_mk(x_146);
x_148 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_127);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_147);
x_150 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_131);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_131);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_131);
x_153 = l_Lean_Syntax_node2(x_131, x_152, x_151, x_5);
lean_inc(x_131);
x_154 = l_Lean_Syntax_node1(x_131, x_138, x_153);
x_155 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_140);
lean_inc(x_131);
x_156 = l_Lean_Syntax_node2(x_131, x_155, x_140, x_154);
x_157 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_131);
x_158 = l_Lean_Syntax_node5(x_131, x_157, x_144, x_149, x_156, x_129, x_140);
x_159 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_160 = l_Lean_Syntax_node2(x_131, x_159, x_142, x_158);
lean_inc(x_160);
x_161 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_161, 0, x_160);
x_162 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_160, x_161, x_9, x_10, x_136);
return x_162;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = !lean_is_exclusive(x_17);
if (x_168 == 0)
{
return x_17;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_17, 0);
x_170 = lean_ctor_get(x_17, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_17);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_elabConfig___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_elabConfig___lambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOptionalNode(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_elabConfig___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___closed__6() {
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
static lean_object* _init_l_Lake_DSL_elabConfig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_elabConfig___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_DSL_optConfig___closed__2;
lean_inc(x_4);
x_9 = l_Lean_Syntax_isOfKind(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lake_DSL_elabConfig___closed__2;
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_10, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_4, x_12);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
x_16 = l_Lean_Syntax_matchesNull(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lake_DSL_elabConfig___closed__2;
x_18 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_17, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_20 = l_Lake_DSL_declValWhere___closed__2;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_DSL_declValStruct___closed__2;
lean_inc(x_19);
x_23 = l_Lean_Syntax_isOfKind(x_19, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lake_DSL_elabConfig___closed__2;
x_25 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_24, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Syntax_getArg(x_19, x_12);
x_27 = l_Lake_DSL_structVal___closed__2;
lean_inc(x_26);
x_28 = l_Lean_Syntax_isOfKind(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lake_DSL_elabConfig___closed__2;
x_30 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_29, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_Lean_Syntax_getArg(x_26, x_12);
x_32 = l_Lean_Syntax_getArg(x_26, x_15);
lean_dec(x_26);
x_33 = l_Lake_DSL_mkConfigFields___closed__1;
lean_inc(x_32);
x_34 = l_Lean_Syntax_isOfKind(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lake_DSL_elabConfig___closed__2;
x_36 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_35, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Syntax_getArg(x_32, x_12);
lean_dec(x_32);
x_38 = l_Lean_Syntax_getArg(x_19, x_15);
lean_dec(x_19);
x_39 = l_Lean_Syntax_isNone(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_inc(x_38);
x_40 = l_Lean_Syntax_matchesNull(x_38, x_15);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lake_DSL_elabConfig___closed__2;
x_42 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_41, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Syntax_getArg(x_38, x_12);
lean_dec(x_38);
x_44 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_43);
x_45 = l_Lean_Syntax_isOfKind(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_Lake_DSL_elabConfig___closed__2;
x_47 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_46, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_box(0);
x_50 = l_Lake_DSL_elabConfig___lambda__1(x_37, x_31, x_1, x_2, x_3, x_4, x_49, x_48, x_5, x_6, x_7);
lean_dec(x_31);
lean_dec(x_37);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = l_Lake_DSL_elabConfig___lambda__1(x_37, x_31, x_1, x_2, x_3, x_4, x_52, x_51, x_5, x_6, x_7);
lean_dec(x_31);
lean_dec(x_37);
return x_53;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_Syntax_getArg(x_19, x_12);
x_55 = l_Lean_Syntax_getArg(x_19, x_15);
x_56 = l_Lake_DSL_mkConfigFields___closed__1;
lean_inc(x_55);
x_57 = l_Lean_Syntax_isOfKind(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = l_Lake_DSL_elabConfig___closed__2;
x_59 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_58, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = l_Lean_Syntax_getArg(x_55, x_12);
lean_dec(x_55);
x_61 = lean_unsigned_to_nat(2u);
x_62 = l_Lean_Syntax_getArg(x_19, x_61);
lean_dec(x_19);
x_63 = l_Lean_Syntax_isNone(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_inc(x_62);
x_64 = l_Lean_Syntax_matchesNull(x_62, x_15);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = l_Lake_DSL_elabConfig___closed__2;
x_66 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_65, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_Syntax_getArg(x_62, x_12);
lean_dec(x_62);
x_68 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_67);
x_69 = l_Lean_Syntax_isOfKind(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = l_Lake_DSL_elabConfig___closed__2;
x_71 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_4, x_70, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_73 = lean_box(0);
x_74 = l_Lake_DSL_elabConfig___lambda__1(x_60, x_54, x_1, x_2, x_3, x_4, x_73, x_72, x_5, x_6, x_7);
lean_dec(x_54);
lean_dec(x_60);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = l_Lake_DSL_elabConfig___lambda__1(x_60, x_54, x_1, x_2, x_3, x_4, x_76, x_75, x_5, x_6, x_7);
lean_dec(x_54);
lean_dec(x_60);
return x_77;
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_13);
x_78 = l_Lake_DSL_expandAttrs___closed__1;
lean_inc(x_5);
x_79 = l_Lake_DSL_mkConfigFields(x_1, x_78, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lake_DSL_elabConfig___closed__5;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lake_DSL_elabConfig___closed__3;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_mk(x_85);
x_87 = lean_box(2);
x_88 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_86);
x_90 = l_Lean_Elab_Command_getRef(x_5, x_6, x_81);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = 0;
x_95 = l_Lean_SourceInfo_fromRef(x_92, x_94);
lean_dec(x_92);
x_96 = l_Lean_Elab_Command_getCurrMacroScope(x_5, x_6, x_93);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_100 = l_Lean_Elab_Command_getMainModule___rarg(x_6, x_98);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_102 = lean_ctor_get(x_100, 1);
x_103 = lean_ctor_get(x_100, 0);
lean_dec(x_103);
x_104 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_105 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_95);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_106, 6);
lean_inc(x_95);
x_108 = l_Lean_Syntax_node6(x_95, x_107, x_106, x_106, x_106, x_106, x_106, x_106);
x_109 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_95);
lean_ctor_set_tag(x_100, 2);
lean_ctor_set(x_100, 1, x_109);
lean_ctor_set(x_100, 0, x_95);
x_110 = l_Lake_DSL_elabConfig___closed__7;
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_110);
lean_ctor_set(x_96, 0, x_2);
x_111 = lean_array_mk(x_96);
x_112 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_87);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_111);
x_114 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_95);
lean_ctor_set_tag(x_90, 2);
lean_ctor_set(x_90, 1, x_114);
lean_ctor_set(x_90, 0, x_95);
x_115 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_95);
x_116 = l_Lean_Syntax_node2(x_95, x_115, x_90, x_3);
lean_inc(x_95);
x_117 = l_Lean_Syntax_node1(x_95, x_104, x_116);
x_118 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_106);
lean_inc(x_95);
x_119 = l_Lean_Syntax_node2(x_95, x_118, x_106, x_117);
x_120 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_95);
x_121 = l_Lean_Syntax_node5(x_95, x_120, x_100, x_113, x_119, x_89, x_106);
x_122 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_123 = l_Lean_Syntax_node2(x_95, x_122, x_108, x_121);
lean_inc(x_123);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_124, 0, x_123);
x_125 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_4, x_123, x_124, x_5, x_6, x_102);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_126 = lean_ctor_get(x_100, 1);
lean_inc(x_126);
lean_dec(x_100);
x_127 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_128 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_95);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_95);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_128);
x_130 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_129, 6);
lean_inc(x_95);
x_131 = l_Lean_Syntax_node6(x_95, x_130, x_129, x_129, x_129, x_129, x_129, x_129);
x_132 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_95);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_95);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lake_DSL_elabConfig___closed__7;
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_134);
lean_ctor_set(x_96, 0, x_2);
x_135 = lean_array_mk(x_96);
x_136 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_87);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_135);
x_138 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_95);
lean_ctor_set_tag(x_90, 2);
lean_ctor_set(x_90, 1, x_138);
lean_ctor_set(x_90, 0, x_95);
x_139 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_95);
x_140 = l_Lean_Syntax_node2(x_95, x_139, x_90, x_3);
lean_inc(x_95);
x_141 = l_Lean_Syntax_node1(x_95, x_127, x_140);
x_142 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_129);
lean_inc(x_95);
x_143 = l_Lean_Syntax_node2(x_95, x_142, x_129, x_141);
x_144 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_95);
x_145 = l_Lean_Syntax_node5(x_95, x_144, x_133, x_137, x_143, x_89, x_129);
x_146 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_147 = l_Lean_Syntax_node2(x_95, x_146, x_131, x_145);
lean_inc(x_147);
x_148 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_148, 0, x_147);
x_149 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_4, x_147, x_148, x_5, x_6, x_126);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_150 = lean_ctor_get(x_96, 1);
lean_inc(x_150);
lean_dec(x_96);
x_151 = l_Lean_Elab_Command_getMainModule___rarg(x_6, x_150);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_155 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_95);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_95);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_155);
x_157 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_156, 6);
lean_inc(x_95);
x_158 = l_Lean_Syntax_node6(x_95, x_157, x_156, x_156, x_156, x_156, x_156, x_156);
x_159 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_95);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(2, 2, 0);
} else {
 x_160 = x_153;
 lean_ctor_set_tag(x_160, 2);
}
lean_ctor_set(x_160, 0, x_95);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lake_DSL_elabConfig___closed__7;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_2);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_mk(x_162);
x_164 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_87);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_95);
lean_ctor_set_tag(x_90, 2);
lean_ctor_set(x_90, 1, x_166);
lean_ctor_set(x_90, 0, x_95);
x_167 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_95);
x_168 = l_Lean_Syntax_node2(x_95, x_167, x_90, x_3);
lean_inc(x_95);
x_169 = l_Lean_Syntax_node1(x_95, x_154, x_168);
x_170 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_156);
lean_inc(x_95);
x_171 = l_Lean_Syntax_node2(x_95, x_170, x_156, x_169);
x_172 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_95);
x_173 = l_Lean_Syntax_node5(x_95, x_172, x_160, x_165, x_171, x_89, x_156);
x_174 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_175 = l_Lean_Syntax_node2(x_95, x_174, x_158, x_173);
lean_inc(x_175);
x_176 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_176, 0, x_175);
x_177 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_4, x_175, x_176, x_5, x_6, x_152);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_178 = lean_ctor_get(x_90, 0);
x_179 = lean_ctor_get(x_90, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_90);
x_180 = 0;
x_181 = l_Lean_SourceInfo_fromRef(x_178, x_180);
lean_dec(x_178);
x_182 = l_Lean_Elab_Command_getCurrMacroScope(x_5, x_6, x_179);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Elab_Command_getMainModule___rarg(x_6, x_183);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_189 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_181);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_181);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set(x_190, 2, x_189);
x_191 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_190, 6);
lean_inc(x_181);
x_192 = l_Lean_Syntax_node6(x_181, x_191, x_190, x_190, x_190, x_190, x_190, x_190);
x_193 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_181);
if (lean_is_scalar(x_187)) {
 x_194 = lean_alloc_ctor(2, 2, 0);
} else {
 x_194 = x_187;
 lean_ctor_set_tag(x_194, 2);
}
lean_ctor_set(x_194, 0, x_181);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lake_DSL_elabConfig___closed__7;
if (lean_is_scalar(x_184)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_184;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_array_mk(x_196);
x_198 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_87);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_199, 2, x_197);
x_200 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_181);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_181);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_181);
x_203 = l_Lean_Syntax_node2(x_181, x_202, x_201, x_3);
lean_inc(x_181);
x_204 = l_Lean_Syntax_node1(x_181, x_188, x_203);
x_205 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_190);
lean_inc(x_181);
x_206 = l_Lean_Syntax_node2(x_181, x_205, x_190, x_204);
x_207 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_181);
x_208 = l_Lean_Syntax_node5(x_181, x_207, x_194, x_199, x_206, x_89, x_190);
x_209 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_210 = l_Lean_Syntax_node2(x_181, x_209, x_192, x_208);
lean_inc(x_210);
x_211 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_211, 0, x_210);
x_212 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_4, x_210, x_211, x_5, x_6, x_186);
return x_212;
}
}
else
{
uint8_t x_213; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_79);
if (x_213 == 0)
{
return x_79;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_79, 0);
x_215 = lean_ctor_get(x_79, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_79);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_DSL_elabConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* initialize_Lake_DSL_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Binder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_packageDeclName___closed__1 = _init_l_Lake_DSL_packageDeclName___closed__1();
lean_mark_persistent(l_Lake_DSL_packageDeclName___closed__1);
l_Lake_DSL_packageDeclName___closed__2 = _init_l_Lake_DSL_packageDeclName___closed__2();
lean_mark_persistent(l_Lake_DSL_packageDeclName___closed__2);
l_Lake_DSL_packageDeclName = _init_l_Lake_DSL_packageDeclName();
lean_mark_persistent(l_Lake_DSL_packageDeclName);
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
l_Lake_DSL_identOrStr___closed__1 = _init_l_Lake_DSL_identOrStr___closed__1();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__1);
l_Lake_DSL_identOrStr___closed__2 = _init_l_Lake_DSL_identOrStr___closed__2();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__2);
l_Lake_DSL_identOrStr___closed__3 = _init_l_Lake_DSL_identOrStr___closed__3();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__3);
l_Lake_DSL_identOrStr___closed__4 = _init_l_Lake_DSL_identOrStr___closed__4();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__4);
l_Lake_DSL_identOrStr___closed__5 = _init_l_Lake_DSL_identOrStr___closed__5();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__5);
l_Lake_DSL_identOrStr___closed__6 = _init_l_Lake_DSL_identOrStr___closed__6();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__6);
l_Lake_DSL_identOrStr___closed__7 = _init_l_Lake_DSL_identOrStr___closed__7();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__7);
l_Lake_DSL_identOrStr___closed__8 = _init_l_Lake_DSL_identOrStr___closed__8();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__8);
l_Lake_DSL_identOrStr___closed__9 = _init_l_Lake_DSL_identOrStr___closed__9();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__9);
l_Lake_DSL_identOrStr___closed__10 = _init_l_Lake_DSL_identOrStr___closed__10();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__10);
l_Lake_DSL_identOrStr___closed__11 = _init_l_Lake_DSL_identOrStr___closed__11();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__11);
l_Lake_DSL_identOrStr___closed__12 = _init_l_Lake_DSL_identOrStr___closed__12();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__12);
l_Lake_DSL_identOrStr___closed__13 = _init_l_Lake_DSL_identOrStr___closed__13();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__13);
l_Lake_DSL_identOrStr___closed__14 = _init_l_Lake_DSL_identOrStr___closed__14();
lean_mark_persistent(l_Lake_DSL_identOrStr___closed__14);
l_Lake_DSL_identOrStr = _init_l_Lake_DSL_identOrStr();
lean_mark_persistent(l_Lake_DSL_identOrStr);
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
l_Lake_DSL_declValDo___closed__16 = _init_l_Lake_DSL_declValDo___closed__16();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__16);
l_Lake_DSL_declValDo___closed__17 = _init_l_Lake_DSL_declValDo___closed__17();
lean_mark_persistent(l_Lake_DSL_declValDo___closed__17);
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
l_Lake_DSL_declValWhere = _init_l_Lake_DSL_declValWhere();
lean_mark_persistent(l_Lake_DSL_declValWhere);
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
l_Lake_DSL_simpleDeclSig___closed__6 = _init_l_Lake_DSL_simpleDeclSig___closed__6();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__6);
l_Lake_DSL_simpleDeclSig___closed__7 = _init_l_Lake_DSL_simpleDeclSig___closed__7();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__7);
l_Lake_DSL_simpleDeclSig___closed__8 = _init_l_Lake_DSL_simpleDeclSig___closed__8();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__8);
l_Lake_DSL_simpleDeclSig___closed__9 = _init_l_Lake_DSL_simpleDeclSig___closed__9();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__9);
l_Lake_DSL_simpleDeclSig___closed__10 = _init_l_Lake_DSL_simpleDeclSig___closed__10();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__10);
l_Lake_DSL_simpleDeclSig___closed__11 = _init_l_Lake_DSL_simpleDeclSig___closed__11();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__11);
l_Lake_DSL_simpleDeclSig___closed__12 = _init_l_Lake_DSL_simpleDeclSig___closed__12();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig___closed__12);
l_Lake_DSL_simpleDeclSig = _init_l_Lake_DSL_simpleDeclSig();
lean_mark_persistent(l_Lake_DSL_simpleDeclSig);
l_Lake_DSL_optConfig___closed__1 = _init_l_Lake_DSL_optConfig___closed__1();
lean_mark_persistent(l_Lake_DSL_optConfig___closed__1);
l_Lake_DSL_optConfig___closed__2 = _init_l_Lake_DSL_optConfig___closed__2();
lean_mark_persistent(l_Lake_DSL_optConfig___closed__2);
l_Lake_DSL_optConfig___closed__3 = _init_l_Lake_DSL_optConfig___closed__3();
lean_mark_persistent(l_Lake_DSL_optConfig___closed__3);
l_Lake_DSL_optConfig___closed__4 = _init_l_Lake_DSL_optConfig___closed__4();
lean_mark_persistent(l_Lake_DSL_optConfig___closed__4);
l_Lake_DSL_optConfig___closed__5 = _init_l_Lake_DSL_optConfig___closed__5();
lean_mark_persistent(l_Lake_DSL_optConfig___closed__5);
l_Lake_DSL_optConfig = _init_l_Lake_DSL_optConfig();
lean_mark_persistent(l_Lake_DSL_optConfig);
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
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__13);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__1);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__2);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__3);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__4);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__5);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__7);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__9);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__10);
l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__11);
l_Lake_DSL_mkConfigFields___closed__1 = _init_l_Lake_DSL_mkConfigFields___closed__1();
lean_mark_persistent(l_Lake_DSL_mkConfigFields___closed__1);
l_Lake_DSL_mkConfigFields___closed__2 = _init_l_Lake_DSL_mkConfigFields___closed__2();
lean_mark_persistent(l_Lake_DSL_mkConfigFields___closed__2);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__1);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_mkConfigDeclIdent___spec__2___closed__2);
l_Lake_DSL_elabConfig___lambda__1___closed__1 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__1);
l_Lake_DSL_elabConfig___lambda__1___closed__2 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__2);
l_Lake_DSL_elabConfig___lambda__1___closed__3 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__3();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__3);
l_Lake_DSL_elabConfig___lambda__1___closed__4 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__4();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__4);
l_Lake_DSL_elabConfig___lambda__1___closed__5 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__5();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__5);
l_Lake_DSL_elabConfig___lambda__1___closed__6 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__6();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__6);
l_Lake_DSL_elabConfig___lambda__1___closed__7 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__7();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__7);
l_Lake_DSL_elabConfig___lambda__1___closed__8 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__8();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__8);
l_Lake_DSL_elabConfig___lambda__1___closed__9 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__9();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__9);
l_Lake_DSL_elabConfig___lambda__1___closed__10 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__10();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__10);
l_Lake_DSL_elabConfig___lambda__1___closed__11 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__11();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__11);
l_Lake_DSL_elabConfig___lambda__1___closed__12 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__12();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__12);
l_Lake_DSL_elabConfig___lambda__1___closed__13 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__13();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__13);
l_Lake_DSL_elabConfig___lambda__1___closed__14 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__14();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__14);
l_Lake_DSL_elabConfig___lambda__1___closed__15 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__15();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__15);
l_Lake_DSL_elabConfig___lambda__1___closed__16 = _init_l_Lake_DSL_elabConfig___lambda__1___closed__16();
lean_mark_persistent(l_Lake_DSL_elabConfig___lambda__1___closed__16);
l_Lake_DSL_elabConfig___closed__1 = _init_l_Lake_DSL_elabConfig___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__1);
l_Lake_DSL_elabConfig___closed__2 = _init_l_Lake_DSL_elabConfig___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__2);
l_Lake_DSL_elabConfig___closed__3 = _init_l_Lake_DSL_elabConfig___closed__3();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__3);
l_Lake_DSL_elabConfig___closed__4 = _init_l_Lake_DSL_elabConfig___closed__4();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__4);
l_Lake_DSL_elabConfig___closed__5 = _init_l_Lake_DSL_elabConfig___closed__5();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__5);
l_Lake_DSL_elabConfig___closed__6 = _init_l_Lake_DSL_elabConfig___closed__6();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__6);
l_Lake_DSL_elabConfig___closed__7 = _init_l_Lake_DSL_elabConfig___closed__7();
lean_mark_persistent(l_Lake_DSL_elabConfig___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
