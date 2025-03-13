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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lake_DSL_simpleDeclSig;
static lean_object* l_Lake_DSL_declValWhere___closed__7;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__13;
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__1___closed__2;
static lean_object* l_Lake_DSL_simpleBinder___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_declValStruct;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__8;
static lean_object* l_Lake_DSL_declValDo___closed__8;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__6;
static lean_object* l_Lake_DSL_identOrStr___closed__9;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__6;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__1;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7;
static lean_object* l_Lake_DSL_simpleBinder___closed__4;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1;
lean_object* l_Lean_TSyntax_getString(lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__12;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
static lean_object* l_Lake_DSL_identOrStr___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__1;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__1___closed__1;
lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_simpleBinder;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__1;
static lean_object* l_Lake_DSL_structDeclSig___closed__7;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__3___closed__3;
static lean_object* l_Lake_DSL_structDeclSig___closed__11;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__2;
static lean_object* l_Lake_DSL_declValDo___closed__3;
static lean_object* l_Lake_DSL_identOrStr___closed__5;
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
static lean_object* l_Lake_DSL_expandAttrs___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_identOrStr;
lean_object* l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__9;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__3___closed__1;
static lean_object* l_Lake_DSL_structVal___closed__2;
static lean_object* l_Lake_DSL_expandAttrs___closed__5;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__12;
static lean_object* l_Lake_DSL_expandAttrs___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
static lean_object* l_Lake_DSL_structVal___closed__7;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__5;
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__5;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__11;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__4;
static lean_object* l_Lake_DSL_expandAttrs___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__4;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
LEAN_EXPORT lean_object* l_Lake_DSL_bracketedSimpleBinder;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_declValWhere;
static lean_object* l_Lake_DSL_identOrStr___closed__8;
static lean_object* l_Lake_DSL_declValStruct___closed__1;
static lean_object* l_Lake_DSL_declValDo___closed__2;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__13;
static lean_object* l_Lake_DSL_declValWhere___closed__4;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__13;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__6;
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8;
static lean_object* l_Lake_DSL_simpleBinder___closed__2;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_structDeclSig;
static lean_object* l_Lake_DSL_declField___closed__7;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__6;
static lean_object* l_Lake_DSL_declValDo___closed__17;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
static lean_object* l_Lake_DSL_simpleBinder___closed__3;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5;
static lean_object* l_Lake_DSL_declValDo___closed__14;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__8;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__11;
static lean_object* l_Lake_DSL_structDeclSig___closed__10;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__4;
static lean_object* l_Lake_DSL_identOrStr___closed__11;
static lean_object* l_Lake_DSL_declValDo___closed__1;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__4;
static lean_object* l_Lake_DSL_structVal___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lake_DSL_structVal;
static lean_object* l_Lake_DSL_structDeclSig___closed__9;
static lean_object* l_Lake_DSL_structVal___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__8;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_declValDo;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__2;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__15;
static lean_object* l_Lake_DSL_declField___closed__12;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__1;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__7;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__7;
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__4;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__6;
static lean_object* l_Lake_DSL_declField___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
static lean_object* l_Lake_DSL_identOrStr___closed__14;
static lean_object* l_Lake_DSL_declValDo___closed__9;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__12;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__12;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__9;
LEAN_EXPORT lean_object* l_Lake_DSL_declField;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___boxed(lean_object**);
static lean_object* l_Lake_DSL_structDeclSig___closed__8;
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__7___closed__2;
static lean_object* l_Lake_DSL_declValWhere___closed__1;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1;
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9;
static lean_object* l_Lake_DSL_declValStruct___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__7;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__5;
static lean_object* l_Lake_DSL_declValWhere___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_DSL_declField___closed__1;
static lean_object* l_Lake_DSL_expandAttrs___closed__4;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_DSL_structVal___closed__14;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__5;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__10;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__4;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
static lean_object* l_Lake_DSL_declField___closed__6;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_DSL_declValDo___closed__5;
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__8;
static lean_object* l_Lake_DSL_declValDo___closed__11;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__1;
static lean_object* l_Lake_DSL_declField___closed__3;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__11;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7;
static lean_object* l_Lake_DSL_declField___closed__2;
static lean_object* l_Lake_DSL_structVal___closed__1;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__17;
static lean_object* l_Lake_DSL_identOrStr___closed__2;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__3___closed__2;
static lean_object* l_Lake_DSL_declValDo___closed__10;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
static lean_object* l_Lake_DSL_declValWhere___closed__5;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structDeclSig___closed__3;
LEAN_EXPORT lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__10;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__3;
static lean_object* l_Lake_DSL_structDeclSig___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__5;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lake_DSL_declValStruct___closed__4;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__16;
static lean_object* l_Lake_DSL_declValDo___closed__13;
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__10;
static lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__14;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structDeclSig", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__1;
x_2 = l_Lake_DSL_identOrStr___closed__2;
x_3 = l_Lake_DSL_structDeclSig___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declValDo___closed__11;
x_2 = l_Lake_DSL_identOrStr;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__6() {
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
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_declValDo___closed__11;
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
x_1 = l_Lake_DSL_declField___closed__4;
x_2 = l_Lake_DSL_structDeclSig___closed__5;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DSL_structDeclSig___closed__4;
x_2 = l_Lake_DSL_structDeclSig___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_identOrStr___closed__6;
x_2 = l_Lake_DSL_structDeclSig___closed__9;
x_3 = l_Lake_DSL_identOrStr;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_structDeclSig___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_DSL_structDeclSig___closed__1;
x_2 = l_Lake_DSL_structDeclSig___closed__2;
x_3 = l_Lake_DSL_structDeclSig___closed__10;
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
x_1 = l_Lake_DSL_structDeclSig___closed__11;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2(x_2, x_3, x_4, x_8);
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
x_23 = l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2(x_2, x_22, x_4, x_8);
return x_23;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed field declaration syntax", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' field '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_9, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_16 = lean_array_uget(x_7, x_9);
lean_inc(x_16);
x_24 = l_Lean_Syntax_isOfKind(x_16, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_1);
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2;
x_26 = l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1(x_16, x_25, x_11, x_12, x_13);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_16, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = l_Lean_Syntax_getArg(x_16, x_33);
x_35 = l_Lean_Syntax_getId(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8;
lean_inc(x_1);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_1);
x_39 = l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(x_38, x_11, x_12, x_13);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_st_ref_get(x_12, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_1);
x_48 = l_Lean_findField_x3f(x_47, x_1, x_35);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_34);
x_49 = 0;
lean_inc(x_1);
x_50 = l_Lean_MessageData_ofConstName(x_1, x_49);
x_51 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_51);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_52);
lean_ctor_set(x_39, 0, x_43);
x_53 = l_Lean_MessageData_ofName(x_35);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = 1;
lean_inc(x_11);
x_58 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_32, x_56, x_57, x_49, x_11, x_12, x_46);
lean_dec(x_32);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_10);
x_17 = x_60;
x_18 = x_59;
goto block_23;
}
else
{
uint8_t x_61; 
lean_free_object(x_39);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_48, 0);
lean_dec(x_62);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 0, x_32);
x_63 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_10, x_35, x_43);
lean_ctor_set(x_48, 0, x_63);
x_17 = x_48;
x_18 = x_46;
goto block_23;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_48);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 0, x_32);
x_64 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_10, x_35, x_43);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_17 = x_65;
x_18 = x_46;
goto block_23;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_1);
x_69 = l_Lean_findField_x3f(x_68, x_1, x_35);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_34);
x_70 = 0;
lean_inc(x_1);
x_71 = l_Lean_MessageData_ofConstName(x_1, x_70);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_74);
lean_ctor_set(x_39, 0, x_73);
x_75 = l_Lean_MessageData_ofName(x_35);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_39);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = 1;
lean_inc(x_11);
x_80 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_32, x_78, x_79, x_70, x_11, x_12, x_67);
lean_dec(x_32);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_10);
x_17 = x_82;
x_18 = x_81;
goto block_23;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_39);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_32);
lean_ctor_set(x_84, 1, x_34);
x_85 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_10, x_35, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
x_17 = x_86;
x_18 = x_67;
goto block_23;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_39, 1);
lean_inc(x_87);
lean_dec(x_39);
x_88 = lean_st_ref_get(x_12, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
lean_inc(x_1);
x_93 = l_Lean_findField_x3f(x_92, x_1, x_35);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_34);
x_94 = 0;
lean_inc(x_1);
x_95 = l_Lean_MessageData_ofConstName(x_1, x_94);
x_96 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(7, 2, 0);
} else {
 x_97 = x_91;
 lean_ctor_set_tag(x_97, 7);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_MessageData_ofName(x_35);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = 1;
lean_inc(x_11);
x_105 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_32, x_103, x_104, x_94, x_11, x_12, x_90);
lean_dec(x_32);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_10);
x_17 = x_107;
x_18 = x_106;
goto block_23;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_108 = x_93;
} else {
 lean_dec_ref(x_93);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_91;
}
lean_ctor_set(x_109, 0, x_32);
lean_ctor_set(x_109, 1, x_34);
x_110 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_10, x_35, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
x_17 = x_111;
x_18 = x_90;
goto block_23;
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_9, x_20);
x_9 = x_21;
x_10 = x_19;
x_13 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_SourceInfo_fromRef(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstField", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstLVal", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1;
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_3 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structInstFieldDef", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_expandAttrs___closed__4;
x_4 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1;
x_2 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4(x_1, x_2, x_8, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 1;
x_18 = l_Lean_mkIdentFrom(x_15, x_9, x_17);
lean_dec(x_15);
x_19 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1;
x_20 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5;
x_21 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7;
x_22 = l_Lean_Syntax_node2(x_19, x_20, x_18, x_21);
x_23 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9;
x_24 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11;
x_25 = l_Lean_Syntax_node2(x_19, x_23, x_24, x_16);
x_26 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_27 = l_Lean_Syntax_node3(x_19, x_26, x_21, x_21, x_25);
x_28 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3;
x_29 = l_Lean_Syntax_node2(x_19, x_28, x_22, x_27);
x_30 = lean_array_push(x_13, x_29);
x_2 = x_30;
x_3 = x_11;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1___boxed), 4, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6(x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; uint8_t x_23; 
x_14 = lean_array_uget(x_5, x_7);
x_22 = l_Lake_DSL_declField___closed__2;
lean_inc(x_14);
x_23 = l_Lean_Syntax_isOfKind(x_14, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2;
x_25 = l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1(x_14, x_24, x_9, x_10, x_11);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_getArg(x_14, x_30);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_14, x_32);
x_34 = l_Lean_Syntax_getId(x_31);
lean_inc(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8;
lean_inc(x_1);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_1);
x_38 = l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(x_37, x_9, x_10, x_11);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_st_ref_get(x_10, x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l_Lean_findField_x3f(x_46, x_1, x_34);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_33);
x_48 = 0;
lean_inc(x_1);
x_49 = l_Lean_MessageData_ofConstName(x_1, x_48);
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_50);
x_51 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_42);
x_52 = l_Lean_MessageData_ofName(x_34);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
lean_inc(x_9);
x_57 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_31, x_55, x_56, x_48, x_9, x_10, x_45);
lean_dec(x_31);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_8);
x_15 = x_59;
x_16 = x_58;
goto block_21;
}
else
{
uint8_t x_60; 
lean_free_object(x_38);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_dec(x_61);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_42, 0, x_31);
x_62 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_34, x_42);
lean_ctor_set(x_47, 0, x_62);
x_15 = x_47;
x_16 = x_45;
goto block_21;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_42, 0, x_31);
x_63 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_34, x_42);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_15 = x_64;
x_16 = x_45;
goto block_21;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_42, 0);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_42);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_1);
x_68 = l_Lean_findField_x3f(x_67, x_1, x_34);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_33);
x_69 = 0;
lean_inc(x_1);
x_70 = l_Lean_MessageData_ofConstName(x_1, x_69);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_73);
lean_ctor_set(x_38, 0, x_72);
x_74 = l_Lean_MessageData_ofName(x_34);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_38);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = 1;
lean_inc(x_9);
x_79 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_31, x_77, x_78, x_69, x_9, x_10, x_66);
lean_dec(x_31);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_8);
x_15 = x_81;
x_16 = x_80;
goto block_21;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_38);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_82 = x_68;
} else {
 lean_dec_ref(x_68);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_31);
lean_ctor_set(x_83, 1, x_33);
x_84 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_34, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
x_15 = x_85;
x_16 = x_66;
goto block_21;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_st_ref_get(x_10, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec(x_88);
lean_inc(x_1);
x_92 = l_Lean_findField_x3f(x_91, x_1, x_34);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_33);
x_93 = 0;
lean_inc(x_1);
x_94 = l_Lean_MessageData_ofConstName(x_1, x_93);
x_95 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10;
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(7, 2, 0);
} else {
 x_96 = x_90;
 lean_ctor_set_tag(x_96, 7);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_MessageData_ofName(x_34);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = 1;
lean_inc(x_9);
x_104 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_31, x_102, x_103, x_93, x_9, x_10, x_89);
lean_dec(x_31);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_8);
x_15 = x_106;
x_16 = x_105;
goto block_21;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_107 = x_92;
} else {
 lean_dec_ref(x_92);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_90;
}
lean_ctor_set(x_108, 0, x_31);
lean_ctor_set(x_108, 1, x_33);
x_109 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_34, x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_109);
x_15 = x_110;
x_16 = x_89;
goto block_21;
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_7, x_18);
x_7 = x_19;
x_8 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8(x_1, x_2, x_8, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 1;
x_18 = l_Lean_mkIdentFrom(x_15, x_9, x_17);
lean_dec(x_15);
x_19 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1;
x_20 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5;
x_21 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7;
x_22 = l_Lean_Syntax_node2(x_19, x_20, x_18, x_21);
x_23 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9;
x_24 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11;
x_25 = l_Lean_Syntax_node2(x_19, x_23, x_24, x_16);
x_26 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_27 = l_Lean_Syntax_node3(x_19, x_26, x_21, x_21, x_25);
x_28 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3;
x_29 = l_Lean_Syntax_node2(x_19, x_28, x_22, x_27);
x_30 = lean_array_push(x_13, x_29);
x_2 = x_30;
x_3 = x_11;
x_6 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed configuration syntax", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DSL_elabConfigDecl___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_DSL_elabConfigDecl___lambda__1___closed__2;
x_7 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("where", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__2() {
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
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_3 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("whereStructInst", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declModifiers", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abbrev", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optDeclSig", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_DSL_expandAttrs___closed__2;
x_2 = l_Lake_DSL_expandAttrs___closed__3;
x_3 = l_Lake_DSL_simpleDeclSig___closed__7;
x_4 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_array_size(x_1);
x_20 = 0;
lean_inc(x_15);
lean_inc(x_2);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3(x_2, x_3, x_4, x_5, x_1, x_18, x_1, x_19, x_20, x_13, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_4);
x_24 = lean_array_mk(x_4);
lean_inc(x_24);
x_25 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4(x_4, x_24, x_22, x_15, x_16, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Elab_Command_getRef(x_15, x_16, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = 0;
x_34 = l_Lean_mkCIdentFrom(x_30, x_2, x_33);
lean_dec(x_30);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = l_Lean_Elab_Command_getRef(x_15, x_16, x_31);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_16);
lean_inc(x_15);
x_289 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5(x_287, x_33, x_15, x_16, x_288);
lean_dec(x_287);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_35 = x_290;
x_36 = x_291;
goto block_285;
}
else
{
uint8_t x_292; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_292 = !lean_is_exclusive(x_289);
if (x_292 == 0)
{
return x_289;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_289, 0);
x_294 = lean_ctor_get(x_289, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_289);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_12, 0);
lean_inc(x_296);
lean_dec(x_12);
x_297 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_296, x_33, x_15, x_16, x_31);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_35 = x_298;
x_36 = x_299;
goto block_285;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_11, 0);
lean_inc(x_300);
lean_dec(x_11);
x_35 = x_300;
x_36 = x_31;
goto block_285;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_11, 0);
lean_inc(x_301);
lean_dec(x_11);
x_302 = lean_ctor_get(x_12, 0);
lean_inc(x_302);
lean_dec(x_12);
x_303 = l_Lean_mkIdentFrom(x_301, x_302, x_33);
lean_dec(x_301);
x_35 = x_303;
x_36 = x_31;
goto block_285;
}
}
block_285:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__1;
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(2, 2, 0);
} else {
 x_38 = x_32;
 lean_ctor_set_tag(x_38, 2);
}
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__3;
x_40 = l_Lean_Syntax_mkSep(x_26, x_39);
lean_dec(x_26);
lean_inc(x_4);
if (lean_is_scalar(x_28)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_28;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_array_mk(x_41);
x_43 = lean_box(2);
x_44 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
x_46 = l_Lean_Elab_Command_getRef(x_15, x_16, x_36);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_281; 
x_281 = lean_box(0);
x_47 = x_281;
goto block_280;
}
else
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_10);
if (x_282 == 0)
{
x_47 = x_10;
goto block_280;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_10, 0);
lean_inc(x_283);
lean_dec(x_10);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_47 = x_284;
goto block_280;
}
}
block_280:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
x_51 = l_Lean_mkOptionalNode(x_47);
lean_dec(x_47);
lean_inc(x_4);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 0, x_51);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_mk(x_53);
x_55 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__5;
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_54);
x_57 = l_Lean_SourceInfo_fromRef(x_49, x_33);
lean_dec(x_49);
x_58 = l_Lean_Elab_Command_getCurrMacroScope(x_15, x_16, x_50);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_58, 1);
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
x_62 = l_Lean_Elab_Command_getMainModule___rarg(x_16, x_60);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_64 = lean_ctor_get(x_62, 1);
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_57);
lean_ctor_set_tag(x_62, 2);
lean_ctor_set(x_62, 1, x_66);
lean_ctor_set(x_62, 0, x_57);
x_67 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_68 = l_Lean_Syntax_SepArray_ofElems(x_67, x_7);
x_69 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_70 = l_Array_append___rarg(x_69, x_68);
lean_dec(x_68);
x_71 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_57);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_70);
x_73 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_57);
lean_ctor_set_tag(x_58, 2);
lean_ctor_set(x_58, 1, x_73);
lean_ctor_set(x_58, 0, x_57);
x_74 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_57);
x_75 = l_Lean_Syntax_node3(x_57, x_74, x_62, x_72, x_58);
lean_inc(x_57);
x_76 = l_Lean_Syntax_node1(x_57, x_71, x_75);
lean_inc(x_57);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_57);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_69);
x_78 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_57);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_43);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_24);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_4);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_35);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_mk(x_82);
x_84 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_43);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
x_86 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_57);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_57);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_57);
x_89 = l_Lean_Syntax_node2(x_57, x_88, x_87, x_34);
lean_inc(x_57);
x_90 = l_Lean_Syntax_node1(x_57, x_71, x_89);
x_91 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_77);
lean_inc(x_57);
x_92 = l_Lean_Syntax_node2(x_57, x_91, x_77, x_90);
x_93 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_57);
x_94 = l_Lean_Syntax_node4(x_57, x_93, x_79, x_85, x_92, x_56);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_57);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_57);
lean_ctor_set(x_96, 1, x_71);
lean_ctor_set(x_96, 2, x_95);
x_97 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_77, 3);
lean_inc(x_57);
x_98 = l_Lean_Syntax_node6(x_57, x_97, x_96, x_76, x_77, x_77, x_77, x_77);
x_99 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_100 = l_Lean_Syntax_node2(x_57, x_99, x_98, x_94);
lean_inc(x_100);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_101, 0, x_100);
x_102 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_100, x_101, x_15, x_16, x_64);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_103 = lean_ctor_get(x_8, 0);
lean_inc(x_103);
lean_dec(x_8);
x_104 = l_Array_mkArray1___rarg(x_103);
x_105 = l_Array_append___rarg(x_69, x_104);
lean_dec(x_104);
lean_inc(x_57);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_57);
lean_ctor_set(x_106, 1, x_71);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_77, 3);
lean_inc(x_57);
x_108 = l_Lean_Syntax_node6(x_57, x_107, x_106, x_76, x_77, x_77, x_77, x_77);
x_109 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_110 = l_Lean_Syntax_node2(x_57, x_109, x_108, x_94);
lean_inc(x_110);
x_111 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_111, 0, x_110);
x_112 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_110, x_111, x_15, x_16, x_64);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_113 = lean_ctor_get(x_62, 1);
lean_inc(x_113);
lean_dec(x_62);
x_114 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_57);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_57);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_117 = l_Lean_Syntax_SepArray_ofElems(x_116, x_7);
x_118 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_119 = l_Array_append___rarg(x_118, x_117);
lean_dec(x_117);
x_120 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_57);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_57);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_119);
x_122 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_57);
lean_ctor_set_tag(x_58, 2);
lean_ctor_set(x_58, 1, x_122);
lean_ctor_set(x_58, 0, x_57);
x_123 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_57);
x_124 = l_Lean_Syntax_node3(x_57, x_123, x_115, x_121, x_58);
lean_inc(x_57);
x_125 = l_Lean_Syntax_node1(x_57, x_120, x_124);
lean_inc(x_57);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_57);
lean_ctor_set(x_126, 1, x_120);
lean_ctor_set(x_126, 2, x_118);
x_127 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_57);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_57);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_43);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_24);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_4);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_35);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_mk(x_131);
x_133 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_43);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_132);
x_135 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_57);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_57);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_57);
x_138 = l_Lean_Syntax_node2(x_57, x_137, x_136, x_34);
lean_inc(x_57);
x_139 = l_Lean_Syntax_node1(x_57, x_120, x_138);
x_140 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_126);
lean_inc(x_57);
x_141 = l_Lean_Syntax_node2(x_57, x_140, x_126, x_139);
x_142 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_57);
x_143 = l_Lean_Syntax_node4(x_57, x_142, x_128, x_134, x_141, x_56);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_57);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_57);
lean_ctor_set(x_145, 1, x_120);
lean_ctor_set(x_145, 2, x_144);
x_146 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_126, 3);
lean_inc(x_57);
x_147 = l_Lean_Syntax_node6(x_57, x_146, x_145, x_125, x_126, x_126, x_126, x_126);
x_148 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_149 = l_Lean_Syntax_node2(x_57, x_148, x_147, x_143);
lean_inc(x_149);
x_150 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_149, x_150, x_15, x_16, x_113);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_8, 0);
lean_inc(x_152);
lean_dec(x_8);
x_153 = l_Array_mkArray1___rarg(x_152);
x_154 = l_Array_append___rarg(x_118, x_153);
lean_dec(x_153);
lean_inc(x_57);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_57);
lean_ctor_set(x_155, 1, x_120);
lean_ctor_set(x_155, 2, x_154);
x_156 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_126, 3);
lean_inc(x_57);
x_157 = l_Lean_Syntax_node6(x_57, x_156, x_155, x_125, x_126, x_126, x_126, x_126);
x_158 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_159 = l_Lean_Syntax_node2(x_57, x_158, x_157, x_143);
lean_inc(x_159);
x_160 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_160, 0, x_159);
x_161 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_159, x_160, x_15, x_16, x_113);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_162 = lean_ctor_get(x_58, 1);
lean_inc(x_162);
lean_dec(x_58);
x_163 = l_Lean_Elab_Command_getMainModule___rarg(x_16, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_57);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(2, 2, 0);
} else {
 x_167 = x_165;
 lean_ctor_set_tag(x_167, 2);
}
lean_ctor_set(x_167, 0, x_57);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_169 = l_Lean_Syntax_SepArray_ofElems(x_168, x_7);
x_170 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_171 = l_Array_append___rarg(x_170, x_169);
lean_dec(x_169);
x_172 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_57);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_57);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_171);
x_174 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_57);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_57);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_57);
x_177 = l_Lean_Syntax_node3(x_57, x_176, x_167, x_173, x_175);
lean_inc(x_57);
x_178 = l_Lean_Syntax_node1(x_57, x_172, x_177);
lean_inc(x_57);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_57);
lean_ctor_set(x_179, 1, x_172);
lean_ctor_set(x_179, 2, x_170);
x_180 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_57);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_57);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_43);
lean_ctor_set(x_182, 1, x_172);
lean_ctor_set(x_182, 2, x_24);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_4);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_35);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_array_mk(x_184);
x_186 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_43);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_185);
x_188 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_57);
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_57);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_57);
x_191 = l_Lean_Syntax_node2(x_57, x_190, x_189, x_34);
lean_inc(x_57);
x_192 = l_Lean_Syntax_node1(x_57, x_172, x_191);
x_193 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_179);
lean_inc(x_57);
x_194 = l_Lean_Syntax_node2(x_57, x_193, x_179, x_192);
x_195 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_57);
x_196 = l_Lean_Syntax_node4(x_57, x_195, x_181, x_187, x_194, x_56);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_57);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_57);
lean_ctor_set(x_198, 1, x_172);
lean_ctor_set(x_198, 2, x_197);
x_199 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_179, 3);
lean_inc(x_57);
x_200 = l_Lean_Syntax_node6(x_57, x_199, x_198, x_178, x_179, x_179, x_179, x_179);
x_201 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_202 = l_Lean_Syntax_node2(x_57, x_201, x_200, x_196);
lean_inc(x_202);
x_203 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_203, 0, x_202);
x_204 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_202, x_203, x_15, x_16, x_164);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_205 = lean_ctor_get(x_8, 0);
lean_inc(x_205);
lean_dec(x_8);
x_206 = l_Array_mkArray1___rarg(x_205);
x_207 = l_Array_append___rarg(x_170, x_206);
lean_dec(x_206);
lean_inc(x_57);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_57);
lean_ctor_set(x_208, 1, x_172);
lean_ctor_set(x_208, 2, x_207);
x_209 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_179, 3);
lean_inc(x_57);
x_210 = l_Lean_Syntax_node6(x_57, x_209, x_208, x_178, x_179, x_179, x_179, x_179);
x_211 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_212 = l_Lean_Syntax_node2(x_57, x_211, x_210, x_196);
lean_inc(x_212);
x_213 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_213, 0, x_212);
x_214 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_212, x_213, x_15, x_16, x_164);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_215 = lean_ctor_get(x_46, 0);
x_216 = lean_ctor_get(x_46, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_46);
x_217 = l_Lean_mkOptionalNode(x_47);
lean_dec(x_47);
lean_inc(x_4);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_4);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_45);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_38);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_array_mk(x_220);
x_222 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__5;
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_43);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_221);
x_224 = l_Lean_SourceInfo_fromRef(x_215, x_33);
lean_dec(x_215);
x_225 = l_Lean_Elab_Command_getCurrMacroScope(x_15, x_16, x_216);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = l_Lean_Elab_Command_getMainModule___rarg(x_16, x_226);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_224);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(2, 2, 0);
} else {
 x_232 = x_230;
 lean_ctor_set_tag(x_232, 2);
}
lean_ctor_set(x_232, 0, x_224);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_234 = l_Lean_Syntax_SepArray_ofElems(x_233, x_7);
x_235 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_236 = l_Array_append___rarg(x_235, x_234);
lean_dec(x_234);
x_237 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_224);
x_238 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_238, 0, x_224);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_236);
x_239 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_224);
if (lean_is_scalar(x_227)) {
 x_240 = lean_alloc_ctor(2, 2, 0);
} else {
 x_240 = x_227;
 lean_ctor_set_tag(x_240, 2);
}
lean_ctor_set(x_240, 0, x_224);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_224);
x_242 = l_Lean_Syntax_node3(x_224, x_241, x_232, x_238, x_240);
lean_inc(x_224);
x_243 = l_Lean_Syntax_node1(x_224, x_237, x_242);
lean_inc(x_224);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_224);
lean_ctor_set(x_244, 1, x_237);
lean_ctor_set(x_244, 2, x_235);
x_245 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_224);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_224);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_43);
lean_ctor_set(x_247, 1, x_237);
lean_ctor_set(x_247, 2, x_24);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_4);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_35);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_array_mk(x_249);
x_251 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_252 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_252, 0, x_43);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_250);
x_253 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_224);
x_254 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_254, 0, x_224);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_224);
x_256 = l_Lean_Syntax_node2(x_224, x_255, x_254, x_34);
lean_inc(x_224);
x_257 = l_Lean_Syntax_node1(x_224, x_237, x_256);
x_258 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_244);
lean_inc(x_224);
x_259 = l_Lean_Syntax_node2(x_224, x_258, x_244, x_257);
x_260 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_224);
x_261 = l_Lean_Syntax_node4(x_224, x_260, x_246, x_252, x_259, x_223);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_262 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_224);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_224);
lean_ctor_set(x_263, 1, x_237);
lean_ctor_set(x_263, 2, x_262);
x_264 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_244, 3);
lean_inc(x_224);
x_265 = l_Lean_Syntax_node6(x_224, x_264, x_263, x_243, x_244, x_244, x_244, x_244);
x_266 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_267 = l_Lean_Syntax_node2(x_224, x_266, x_265, x_261);
lean_inc(x_267);
x_268 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_268, 0, x_267);
x_269 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_267, x_268, x_15, x_16, x_229);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_8, 0);
lean_inc(x_270);
lean_dec(x_8);
x_271 = l_Array_mkArray1___rarg(x_270);
x_272 = l_Array_append___rarg(x_235, x_271);
lean_dec(x_271);
lean_inc(x_224);
x_273 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_273, 0, x_224);
lean_ctor_set(x_273, 1, x_237);
lean_ctor_set(x_273, 2, x_272);
x_274 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_244, 3);
lean_inc(x_224);
x_275 = l_Lean_Syntax_node6(x_224, x_274, x_273, x_243, x_244, x_244, x_244, x_244);
x_276 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_277 = l_Lean_Syntax_node2(x_224, x_276, x_275, x_261);
lean_inc(x_277);
x_278 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_278, 0, x_277);
x_279 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_9, x_277, x_278, x_15, x_16, x_229);
return x_279;
}
}
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_304 = !lean_is_exclusive(x_21);
if (x_304 == 0)
{
return x_21;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_21, 0);
x_306 = lean_ctor_get(x_21, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_21);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_declField___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DSL_elabConfigDecl___lambda__3___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_Syntax_getHeadInfo(x_7);
x_14 = lean_box(0);
x_15 = l_Lean_Syntax_TSepArray_getElems___rarg(x_8);
x_16 = lean_box(0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_17 = x_33;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = l_Lake_DSL_expandIdentOrStrAsIdent(x_35);
lean_ctor_set(x_6, 0, x_36);
x_17 = x_6;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
lean_dec(x_6);
x_38 = l_Lake_DSL_expandIdentOrStrAsIdent(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_17 = x_39;
goto block_32;
}
}
block_32:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lake_DSL_declField___closed__2;
x_19 = l_Lake_DSL_elabConfigDecl___lambda__3___closed__1;
x_20 = lean_box(0);
x_21 = l_Lake_DSL_elabConfigDecl___lambda__2(x_15, x_1, x_18, x_14, x_19, x_13, x_2, x_3, x_4, x_9, x_17, x_5, x_16, x_20, x_10, x_11, x_12);
lean_dec(x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = l_Lean_Syntax_getId(x_22);
x_24 = l_Lake_Name_quoteFrom(x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lake_DSL_elabConfigDecl___lambda__3___closed__3;
x_27 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_16, x_26, x_25);
x_28 = l_Lake_DSL_declField___closed__2;
x_29 = l_Lake_DSL_elabConfigDecl___lambda__3___closed__1;
x_30 = lean_box(0);
x_31 = l_Lake_DSL_elabConfigDecl___lambda__2(x_15, x_1, x_28, x_14, x_29, x_13, x_2, x_3, x_4, x_9, x_17, x_5, x_27, x_30, x_10, x_11, x_12);
lean_dec(x_15);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Syntax_getArgs(x_1);
x_11 = lean_apply_7(x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_matchesNull(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_4(x_2, x_12, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_10, x_14);
lean_dec(x_10);
x_16 = l_Lake_DSL_declValWhere___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lake_DSL_declValStruct___closed__2;
lean_inc(x_15);
x_19 = l_Lean_Syntax_isOfKind(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_apply_4(x_2, x_20, x_6, x_7, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Syntax_getArg(x_15, x_14);
x_23 = l_Lake_DSL_structVal___closed__2;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_apply_4(x_2, x_25, x_6, x_7, x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_Syntax_getArg(x_22, x_14);
x_28 = l_Lean_Syntax_getArg(x_22, x_9);
lean_dec(x_22);
x_29 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_apply_4(x_2, x_31, x_6, x_7, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Syntax_getArg(x_28, x_14);
lean_dec(x_28);
x_34 = l_Lean_Syntax_getArg(x_15, x_9);
lean_dec(x_15);
x_35 = l_Lean_Syntax_isNone(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_34);
x_36 = l_Lean_Syntax_matchesNull(x_34, x_9);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_3);
x_37 = lean_box(0);
x_38 = lean_apply_4(x_2, x_37, x_6, x_7, x_8);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Syntax_getArg(x_34, x_14);
lean_dec(x_34);
x_40 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_39);
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_3);
x_42 = lean_box(0);
x_43 = lean_apply_4(x_2, x_42, x_6, x_7, x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_45 = lean_box(0);
x_46 = l_Lake_DSL_elabConfigDecl___lambda__4(x_33, x_3, x_5, x_27, x_45, x_44, x_6, x_7, x_8);
lean_dec(x_33);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = l_Lake_DSL_elabConfigDecl___lambda__4(x_33, x_3, x_5, x_27, x_48, x_47, x_6, x_7, x_8);
lean_dec(x_33);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Syntax_getArg(x_15, x_14);
x_51 = l_Lean_Syntax_getArg(x_15, x_9);
x_52 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
lean_inc(x_51);
x_53 = l_Lean_Syntax_isOfKind(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_54 = lean_box(0);
x_55 = lean_apply_4(x_2, x_54, x_6, x_7, x_8);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = l_Lean_Syntax_getArg(x_51, x_14);
lean_dec(x_51);
x_57 = lean_unsigned_to_nat(2u);
x_58 = l_Lean_Syntax_getArg(x_15, x_57);
lean_dec(x_15);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_inc(x_58);
x_60 = l_Lean_Syntax_matchesNull(x_58, x_9);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
x_61 = lean_box(0);
x_62 = lean_apply_4(x_2, x_61, x_6, x_7, x_8);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Syntax_getArg(x_58, x_14);
lean_dec(x_58);
x_64 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_63);
x_65 = l_Lean_Syntax_isOfKind(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_56);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_3);
x_66 = lean_box(0);
x_67 = lean_apply_4(x_2, x_66, x_6, x_7, x_8);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_69 = lean_box(0);
x_70 = l_Lake_DSL_elabConfigDecl___lambda__4(x_56, x_3, x_5, x_50, x_69, x_68, x_6, x_7, x_8);
lean_dec(x_56);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_58);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_box(0);
x_73 = l_Lake_DSL_elabConfigDecl___lambda__4(x_56, x_3, x_5, x_50, x_72, x_71, x_6, x_7, x_8);
lean_dec(x_56);
return x_73;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_10 = l_Lean_Syntax_matchesNull(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_2, x_11, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lake_DSL_declValWhere___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lake_DSL_declValStruct___closed__2;
lean_inc(x_14);
x_18 = l_Lean_Syntax_isOfKind(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = lean_apply_4(x_2, x_19, x_6, x_7, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Syntax_getArg(x_14, x_13);
x_22 = l_Lake_DSL_structVal___closed__2;
lean_inc(x_21);
x_23 = l_Lean_Syntax_isOfKind(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_apply_4(x_2, x_24, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Syntax_getArg(x_21, x_13);
x_27 = l_Lean_Syntax_getArg(x_21, x_9);
lean_dec(x_21);
x_28 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_apply_4(x_2, x_30, x_6, x_7, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Syntax_getArg(x_27, x_13);
lean_dec(x_27);
x_33 = l_Lean_Syntax_getArg(x_14, x_9);
lean_dec(x_14);
x_34 = l_Lean_Syntax_isNone(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc(x_33);
x_35 = l_Lean_Syntax_matchesNull(x_33, x_9);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_apply_4(x_2, x_36, x_6, x_7, x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Syntax_getArg(x_33, x_13);
lean_dec(x_33);
x_39 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = lean_apply_4(x_2, x_41, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_44 = lean_box(0);
x_45 = l_Lake_DSL_elabConfigDecl___lambda__4(x_32, x_3, x_5, x_26, x_44, x_43, x_6, x_7, x_8);
lean_dec(x_32);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_33);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_box(0);
x_48 = l_Lake_DSL_elabConfigDecl___lambda__4(x_32, x_3, x_5, x_26, x_47, x_46, x_6, x_7, x_8);
lean_dec(x_32);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = l_Lean_Syntax_getArg(x_14, x_13);
x_50 = l_Lean_Syntax_getArg(x_14, x_9);
x_51 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
x_53 = lean_box(0);
x_54 = lean_apply_4(x_2, x_53, x_6, x_7, x_8);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArg(x_50, x_13);
lean_dec(x_50);
x_56 = lean_unsigned_to_nat(2u);
x_57 = l_Lean_Syntax_getArg(x_14, x_56);
lean_dec(x_14);
x_58 = l_Lean_Syntax_isNone(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_inc(x_57);
x_59 = l_Lean_Syntax_matchesNull(x_57, x_9);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_3);
x_60 = lean_box(0);
x_61 = lean_apply_4(x_2, x_60, x_6, x_7, x_8);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Syntax_getArg(x_57, x_13);
lean_dec(x_57);
x_63 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_62);
x_64 = l_Lean_Syntax_isOfKind(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_3);
x_65 = lean_box(0);
x_66 = lean_apply_4(x_2, x_65, x_6, x_7, x_8);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_68 = lean_box(0);
x_69 = l_Lake_DSL_elabConfigDecl___lambda__4(x_55, x_3, x_5, x_49, x_68, x_67, x_6, x_7, x_8);
lean_dec(x_55);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_57);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = l_Lake_DSL_elabConfigDecl___lambda__4(x_55, x_3, x_5, x_49, x_71, x_70, x_6, x_7, x_8);
lean_dec(x_55);
return x_72;
}
}
}
}
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DSL_elabConfigDecl___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOptionalNode(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_size(x_1);
x_16 = 0;
lean_inc(x_11);
lean_inc(x_2);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7(x_2, x_3, x_1, x_14, x_1, x_15, x_16, x_9, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8(x_3, x_1, x_18, x_11, x_12, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Elab_Command_getRef(x_11, x_12, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = 0;
x_29 = l_Lean_mkCIdentFrom(x_25, x_2, x_28);
lean_dec(x_25);
if (lean_obj_tag(x_7) == 0)
{
x_30 = x_8;
x_31 = x_26;
goto block_264;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_7, 0);
lean_inc(x_265);
lean_dec(x_7);
x_266 = l_Lean_mkIdentFrom(x_8, x_265, x_28);
lean_dec(x_8);
x_30 = x_266;
x_31 = x_26;
goto block_264;
}
block_264:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_32 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__3;
x_33 = l_Lean_Syntax_mkSep(x_21, x_32);
lean_dec(x_21);
lean_inc(x_3);
if (lean_is_scalar(x_27)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_27;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_35 = lean_array_mk(x_34);
x_36 = lean_box(2);
x_37 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__2;
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = l_Lake_DSL_elabConfigDecl___lambda__7___closed__2;
lean_inc(x_3);
if (lean_is_scalar(x_23)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_23;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lake_DSL_elabConfigDecl___lambda__7___closed__1;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_mk(x_43);
x_45 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__5;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_44);
x_47 = l_Lean_Elab_Command_getRef(x_11, x_12, x_31);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_Lean_SourceInfo_fromRef(x_49, x_28);
lean_dec(x_49);
x_52 = l_Lean_Elab_Command_getCurrMacroScope(x_11, x_12, x_50);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = l_Lean_Elab_Command_getMainModule___rarg(x_12, x_54);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_51);
lean_ctor_set_tag(x_56, 2);
lean_ctor_set(x_56, 1, x_60);
lean_ctor_set(x_56, 0, x_51);
x_61 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_62 = l_Lean_Syntax_SepArray_ofElems(x_61, x_4);
x_63 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_64 = l_Array_append___rarg(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_51);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
x_67 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_51);
lean_ctor_set_tag(x_52, 2);
lean_ctor_set(x_52, 1, x_67);
lean_ctor_set(x_52, 0, x_51);
x_68 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_51);
x_69 = l_Lean_Syntax_node3(x_51, x_68, x_56, x_66, x_52);
lean_inc(x_51);
x_70 = l_Lean_Syntax_node1(x_51, x_65, x_69);
lean_inc(x_51);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_51);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_63);
x_72 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_51);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_72);
lean_ctor_set(x_47, 0, x_51);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_36);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_1);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_30);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_mk(x_75);
x_77 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_36);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_76);
x_79 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_51);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_51);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_51);
x_82 = l_Lean_Syntax_node2(x_51, x_81, x_80, x_29);
lean_inc(x_51);
x_83 = l_Lean_Syntax_node1(x_51, x_65, x_82);
x_84 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_71);
lean_inc(x_51);
x_85 = l_Lean_Syntax_node2(x_51, x_84, x_71, x_83);
x_86 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_51);
x_87 = l_Lean_Syntax_node4(x_51, x_86, x_47, x_78, x_85, x_46);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_51);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_51);
lean_ctor_set(x_89, 1, x_65);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_71, 3);
lean_inc(x_51);
x_91 = l_Lean_Syntax_node6(x_51, x_90, x_89, x_70, x_71, x_71, x_71, x_71);
x_92 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_93 = l_Lean_Syntax_node2(x_51, x_92, x_91, x_87);
lean_inc(x_93);
x_94 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_94, 0, x_93);
x_95 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_93, x_94, x_11, x_12, x_58);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_5, 0);
lean_inc(x_96);
lean_dec(x_5);
x_97 = l_Array_mkArray1___rarg(x_96);
x_98 = l_Array_append___rarg(x_63, x_97);
lean_dec(x_97);
lean_inc(x_51);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_51);
lean_ctor_set(x_99, 1, x_65);
lean_ctor_set(x_99, 2, x_98);
x_100 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_71, 3);
lean_inc(x_51);
x_101 = l_Lean_Syntax_node6(x_51, x_100, x_99, x_70, x_71, x_71, x_71, x_71);
x_102 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_103 = l_Lean_Syntax_node2(x_51, x_102, x_101, x_87);
lean_inc(x_103);
x_104 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_104, 0, x_103);
x_105 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_103, x_104, x_11, x_12, x_58);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_106 = lean_ctor_get(x_56, 1);
lean_inc(x_106);
lean_dec(x_56);
x_107 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_51);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_51);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_110 = l_Lean_Syntax_SepArray_ofElems(x_109, x_4);
x_111 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_112 = l_Array_append___rarg(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_51);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_51);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_112);
x_115 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_51);
lean_ctor_set_tag(x_52, 2);
lean_ctor_set(x_52, 1, x_115);
lean_ctor_set(x_52, 0, x_51);
x_116 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_51);
x_117 = l_Lean_Syntax_node3(x_51, x_116, x_108, x_114, x_52);
lean_inc(x_51);
x_118 = l_Lean_Syntax_node1(x_51, x_113, x_117);
lean_inc(x_51);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_51);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_111);
x_120 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_51);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_120);
lean_ctor_set(x_47, 0, x_51);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_36);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_1);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_3);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_30);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_mk(x_123);
x_125 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_36);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_124);
x_127 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_51);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_51);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_51);
x_130 = l_Lean_Syntax_node2(x_51, x_129, x_128, x_29);
lean_inc(x_51);
x_131 = l_Lean_Syntax_node1(x_51, x_113, x_130);
x_132 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_119);
lean_inc(x_51);
x_133 = l_Lean_Syntax_node2(x_51, x_132, x_119, x_131);
x_134 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_51);
x_135 = l_Lean_Syntax_node4(x_51, x_134, x_47, x_126, x_133, x_46);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_51);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_51);
lean_ctor_set(x_137, 1, x_113);
lean_ctor_set(x_137, 2, x_136);
x_138 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_119, 3);
lean_inc(x_51);
x_139 = l_Lean_Syntax_node6(x_51, x_138, x_137, x_118, x_119, x_119, x_119, x_119);
x_140 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_141 = l_Lean_Syntax_node2(x_51, x_140, x_139, x_135);
lean_inc(x_141);
x_142 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_142, 0, x_141);
x_143 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_141, x_142, x_11, x_12, x_106);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_5, 0);
lean_inc(x_144);
lean_dec(x_5);
x_145 = l_Array_mkArray1___rarg(x_144);
x_146 = l_Array_append___rarg(x_111, x_145);
lean_dec(x_145);
lean_inc(x_51);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_51);
lean_ctor_set(x_147, 1, x_113);
lean_ctor_set(x_147, 2, x_146);
x_148 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_119, 3);
lean_inc(x_51);
x_149 = l_Lean_Syntax_node6(x_51, x_148, x_147, x_118, x_119, x_119, x_119, x_119);
x_150 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_151 = l_Lean_Syntax_node2(x_51, x_150, x_149, x_135);
lean_inc(x_151);
x_152 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_152, 0, x_151);
x_153 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_151, x_152, x_11, x_12, x_106);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_154 = lean_ctor_get(x_52, 1);
lean_inc(x_154);
lean_dec(x_52);
x_155 = l_Lean_Elab_Command_getMainModule___rarg(x_12, x_154);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_51);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(2, 2, 0);
} else {
 x_159 = x_157;
 lean_ctor_set_tag(x_159, 2);
}
lean_ctor_set(x_159, 0, x_51);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_161 = l_Lean_Syntax_SepArray_ofElems(x_160, x_4);
x_162 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_163 = l_Array_append___rarg(x_162, x_161);
lean_dec(x_161);
x_164 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_51);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_51);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_51);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_51);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_51);
x_169 = l_Lean_Syntax_node3(x_51, x_168, x_159, x_165, x_167);
lean_inc(x_51);
x_170 = l_Lean_Syntax_node1(x_51, x_164, x_169);
lean_inc(x_51);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_51);
lean_ctor_set(x_171, 1, x_164);
lean_ctor_set(x_171, 2, x_162);
x_172 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_51);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_172);
lean_ctor_set(x_47, 0, x_51);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_36);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_1);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_3);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_30);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_mk(x_175);
x_177 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_36);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_176);
x_179 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_51);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_51);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_51);
x_182 = l_Lean_Syntax_node2(x_51, x_181, x_180, x_29);
lean_inc(x_51);
x_183 = l_Lean_Syntax_node1(x_51, x_164, x_182);
x_184 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_171);
lean_inc(x_51);
x_185 = l_Lean_Syntax_node2(x_51, x_184, x_171, x_183);
x_186 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_51);
x_187 = l_Lean_Syntax_node4(x_51, x_186, x_47, x_178, x_185, x_46);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_188 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_51);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_51);
lean_ctor_set(x_189, 1, x_164);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_171, 3);
lean_inc(x_51);
x_191 = l_Lean_Syntax_node6(x_51, x_190, x_189, x_170, x_171, x_171, x_171, x_171);
x_192 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_193 = l_Lean_Syntax_node2(x_51, x_192, x_191, x_187);
lean_inc(x_193);
x_194 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_194, 0, x_193);
x_195 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_193, x_194, x_11, x_12, x_156);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_196 = lean_ctor_get(x_5, 0);
lean_inc(x_196);
lean_dec(x_5);
x_197 = l_Array_mkArray1___rarg(x_196);
x_198 = l_Array_append___rarg(x_162, x_197);
lean_dec(x_197);
lean_inc(x_51);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_51);
lean_ctor_set(x_199, 1, x_164);
lean_ctor_set(x_199, 2, x_198);
x_200 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_171, 3);
lean_inc(x_51);
x_201 = l_Lean_Syntax_node6(x_51, x_200, x_199, x_170, x_171, x_171, x_171, x_171);
x_202 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_203 = l_Lean_Syntax_node2(x_51, x_202, x_201, x_187);
lean_inc(x_203);
x_204 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_204, 0, x_203);
x_205 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_203, x_204, x_11, x_12, x_156);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_206 = lean_ctor_get(x_47, 0);
x_207 = lean_ctor_get(x_47, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_47);
x_208 = l_Lean_SourceInfo_fromRef(x_206, x_28);
lean_dec(x_206);
x_209 = l_Lean_Elab_Command_getCurrMacroScope(x_11, x_12, x_207);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = l_Lean_Elab_Command_getMainModule___rarg(x_12, x_210);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__10;
lean_inc(x_208);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(2, 2, 0);
} else {
 x_216 = x_214;
 lean_ctor_set_tag(x_216, 2);
}
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__11;
x_218 = l_Lean_Syntax_SepArray_ofElems(x_217, x_4);
x_219 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6;
x_220 = l_Array_append___rarg(x_219, x_218);
lean_dec(x_218);
x_221 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
lean_inc(x_208);
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_208);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set(x_222, 2, x_220);
x_223 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__12;
lean_inc(x_208);
if (lean_is_scalar(x_211)) {
 x_224 = lean_alloc_ctor(2, 2, 0);
} else {
 x_224 = x_211;
 lean_ctor_set_tag(x_224, 2);
}
lean_ctor_set(x_224, 0, x_208);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lake_DSL_expandAttrs___closed__6;
lean_inc(x_208);
x_226 = l_Lean_Syntax_node3(x_208, x_225, x_216, x_222, x_224);
lean_inc(x_208);
x_227 = l_Lean_Syntax_node1(x_208, x_221, x_226);
lean_inc(x_208);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_208);
lean_ctor_set(x_228, 1, x_221);
lean_ctor_set(x_228, 2, x_219);
x_229 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__13;
lean_inc(x_208);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_208);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_36);
lean_ctor_set(x_231, 1, x_221);
lean_ctor_set(x_231, 2, x_1);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_3);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_30);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_array_mk(x_233);
x_235 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__16;
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_36);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_236, 2, x_234);
x_237 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_208);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_208);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_208);
x_240 = l_Lean_Syntax_node2(x_208, x_239, x_238, x_29);
lean_inc(x_208);
x_241 = l_Lean_Syntax_node1(x_208, x_221, x_240);
x_242 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__18;
lean_inc(x_228);
lean_inc(x_208);
x_243 = l_Lean_Syntax_node2(x_208, x_242, x_228, x_241);
x_244 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__14;
lean_inc(x_208);
x_245 = l_Lean_Syntax_node4(x_208, x_244, x_230, x_236, x_243, x_46);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_246 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__19;
lean_inc(x_208);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_208);
lean_ctor_set(x_247, 1, x_221);
lean_ctor_set(x_247, 2, x_246);
x_248 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_228, 3);
lean_inc(x_208);
x_249 = l_Lean_Syntax_node6(x_208, x_248, x_247, x_227, x_228, x_228, x_228, x_228);
x_250 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_251 = l_Lean_Syntax_node2(x_208, x_250, x_249, x_245);
lean_inc(x_251);
x_252 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_252, 0, x_251);
x_253 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_251, x_252, x_11, x_12, x_213);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_254 = lean_ctor_get(x_5, 0);
lean_inc(x_254);
lean_dec(x_5);
x_255 = l_Array_mkArray1___rarg(x_254);
x_256 = l_Array_append___rarg(x_219, x_255);
lean_dec(x_255);
lean_inc(x_208);
x_257 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_257, 0, x_208);
lean_ctor_set(x_257, 1, x_221);
lean_ctor_set(x_257, 2, x_256);
x_258 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__9;
lean_inc_n(x_228, 3);
lean_inc(x_208);
x_259 = l_Lean_Syntax_node6(x_208, x_258, x_257, x_227, x_228, x_228, x_228, x_228);
x_260 = l_Lake_DSL_elabConfigDecl___lambda__2___closed__7;
x_261 = l_Lean_Syntax_node2(x_208, x_260, x_259, x_245);
lean_inc(x_261);
x_262 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_262, 0, x_261);
x_263 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_6, x_261, x_262, x_11, x_12, x_213);
return x_263;
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_17);
if (x_267 == 0)
{
return x_17;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_17, 0);
x_269 = lean_ctor_get(x_17, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_17);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_DSL_structDeclSig___closed__2;
lean_inc(x_2);
x_10 = l_Lean_Syntax_isOfKind(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lake_DSL_elabConfigDecl___lambda__1___closed__2;
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_2, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lake_DSL_structDeclSig___closed__4;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lake_DSL_elabConfigDecl___lambda__1___closed__2;
x_18 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_2, x_17, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Syntax_getArg(x_14, x_13);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_DSL_elabConfigDecl___lambda__1___boxed), 5, 1);
lean_closure_set(x_20, 0, x_2);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_DSL_elabConfigDecl___lambda__3___boxed), 12, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_5);
x_22 = lean_unsigned_to_nat(1u);
lean_inc(x_19);
x_23 = l_Lean_Syntax_matchesNull(x_19, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l_Lean_Syntax_isNone(x_19);
lean_dec(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = l_Lake_DSL_elabConfigDecl___lambda__1(x_2, x_25, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = l_Lake_DSL_elabConfigDecl___lambda__5(x_14, x_20, x_21, x_28, x_27, x_6, x_7, x_8);
lean_dec(x_14);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Syntax_getArg(x_19, x_13);
x_31 = l_Lake_DSL_identOrStr___closed__4;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_Syntax_getArg(x_14, x_22);
lean_dec(x_14);
x_34 = l_Lean_Syntax_isNone(x_19);
lean_dec(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = lean_box(0);
x_37 = l_Lake_DSL_elabConfigDecl___lambda__6(x_33, x_20, x_21, x_36, x_35, x_6, x_7, x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = l_Lake_DSL_elabConfigDecl___lambda__6(x_33, x_20, x_21, x_39, x_38, x_6, x_7, x_8);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Syntax_getArg(x_14, x_22);
lean_dec(x_14);
lean_inc(x_41);
x_42 = l_Lean_Syntax_matchesNull(x_41, x_13);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_Syntax_isNone(x_19);
lean_dec(x_19);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_30);
x_45 = lean_box(0);
x_46 = l_Lake_DSL_elabConfigDecl___lambda__6(x_41, x_20, x_21, x_45, x_44, x_6, x_7, x_8);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_30);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = l_Lake_DSL_elabConfigDecl___lambda__6(x_41, x_20, x_21, x_48, x_47, x_6, x_7, x_8);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = l_Lake_DSL_expandIdentOrStrAsIdent(x_30);
x_53 = l_Lean_Syntax_getId(x_52);
x_54 = l_Lake_Name_quoteFrom(x_52, x_53);
lean_inc(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lake_DSL_elabConfigDecl___lambda__3___closed__3;
x_57 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_51, x_56, x_55);
x_58 = l_Lake_DSL_expandAttrs___closed__1;
x_59 = lean_box(0);
x_60 = l_Lake_DSL_elabConfigDecl___lambda__7(x_58, x_1, x_50, x_4, x_3, x_2, x_5, x_52, x_57, x_59, x_6, x_7, x_8);
lean_dec(x_4);
return x_60;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lake_DSL_elabConfigDecl___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lake_DSL_elabConfigDecl___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_DSL_elabConfigDecl___spec__5(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__7(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_DSL_elabConfigDecl___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lake_DSL_elabConfigDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_DSL_elabConfigDecl___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_DSL_elabConfigDecl___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_elabConfigDecl___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_elabConfigDecl___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfigDecl___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_DSL_elabConfigDecl___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_4);
return x_14;
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
l_Lake_DSL_structDeclSig___closed__10 = _init_l_Lake_DSL_structDeclSig___closed__10();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__10);
l_Lake_DSL_structDeclSig___closed__11 = _init_l_Lake_DSL_structDeclSig___closed__11();
lean_mark_persistent(l_Lake_DSL_structDeclSig___closed__11);
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
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__11);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__12);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__13);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_elabConfigDecl___spec__3___closed__14);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__1);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__2);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__3);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__4);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__5);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__6);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__7);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__8);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__9);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__10);
l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11 = _init_l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lake_DSL_elabConfigDecl___spec__4___closed__11);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__1);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_DSL_elabConfigDecl___spec__6___closed__2);
l_Lake_DSL_elabConfigDecl___lambda__1___closed__1 = _init_l_Lake_DSL_elabConfigDecl___lambda__1___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__1___closed__1);
l_Lake_DSL_elabConfigDecl___lambda__1___closed__2 = _init_l_Lake_DSL_elabConfigDecl___lambda__1___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__1___closed__2);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__1 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__1);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__2 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__2);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__3 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__3();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__3);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__4 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__4();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__4);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__5 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__5();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__5);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__6 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__6();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__6);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__7 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__7();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__7);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__8 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__8();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__8);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__9 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__9();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__9);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__10 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__10();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__10);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__11 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__11();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__11);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__12 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__12();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__12);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__13 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__13();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__13);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__14 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__14();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__14);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__15 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__15();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__15);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__16 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__16();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__16);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__17 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__17();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__17);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__18 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__18();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__18);
l_Lake_DSL_elabConfigDecl___lambda__2___closed__19 = _init_l_Lake_DSL_elabConfigDecl___lambda__2___closed__19();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__2___closed__19);
l_Lake_DSL_elabConfigDecl___lambda__3___closed__1 = _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__3___closed__1);
l_Lake_DSL_elabConfigDecl___lambda__3___closed__2 = _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__3___closed__2);
l_Lake_DSL_elabConfigDecl___lambda__3___closed__3 = _init_l_Lake_DSL_elabConfigDecl___lambda__3___closed__3();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__3___closed__3);
l_Lake_DSL_elabConfigDecl___lambda__7___closed__1 = _init_l_Lake_DSL_elabConfigDecl___lambda__7___closed__1();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__7___closed__1);
l_Lake_DSL_elabConfigDecl___lambda__7___closed__2 = _init_l_Lake_DSL_elabConfigDecl___lambda__7___closed__2();
lean_mark_persistent(l_Lake_DSL_elabConfigDecl___lambda__7___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
