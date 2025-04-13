// Lean compiler output
// Module: Lake.DSL.DeclUtil
// Imports: Lake.DSL.Config Lake.Util.Binder Lake.Util.Name Lake.Config.Meta Lean.Parser.Command Lean.Elab.Command
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19;
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
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleDeclSig___closed__10;
static lean_object* l_Lake_DSL_structVal___closed__6;
static lean_object* l_Lake_DSL_structVal___closed__13;
static lean_object* l_Lake_DSL_declValWhere___closed__4;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21;
static lean_object* l_Lake_DSL_elabConfig___closed__6;
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__13;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__11;
static lean_object* l_Lake_DSL_identOrStr___closed__12;
static lean_object* l_Lake_DSL_identOrStr___closed__6;
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_simpleBinder___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declField___closed__7;
static lean_object* l_Lake_DSL_packageDeclName___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16;
LEAN_EXPORT lean_object* l_Lake_DSL_expandAttrs(lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_structVal___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_elabConfig___lambda__1___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__1;
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__1;
static lean_object* l_Lake_DSL_elabConfig___closed__1;
static lean_object* l_Lake_DSL_declValStruct___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValWhere___closed__3;
static lean_object* l_Lake_DSL_structVal___closed__15;
static lean_object* l_Lake_DSL_declValDo___closed__7;
static lean_object* l_Lake_DSL_simpleDeclSig___closed__5;
static lean_object* l_Lake_DSL_optConfig___closed__2;
static lean_object* l_Lake_DSL_declValWhere___closed__2;
static lean_object* l_Lake_DSL_identOrStr___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DSL_declValDo___closed__10;
static lean_object* l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_DSL_bracketedSimpleBinder___closed__3;
static lean_object* l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22;
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_DSL_identOrStr___closed__10;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_3, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("redefined field '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' ('", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is an alias of '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("')", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__2;
x_25 = l_Lean_throwErrorAt___at_Lake_DSL_mkConfigFields___spec__1(x_14, x_24, x_9, x_10, x_11);
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
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__8;
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_34);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_33);
x_43 = 0;
lean_inc(x_1);
x_44 = l_Lean_MessageData_ofConstName(x_1, x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_44);
lean_ctor_set(x_38, 0, x_45);
x_46 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofName(x_34);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
lean_inc(x_9);
x_53 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_31, x_51, x_52, x_43, x_9, x_10, x_40);
lean_dec(x_31);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_8);
x_15 = x_55;
x_16 = x_54;
goto block_21;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*2);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_NameMap_contains___rarg(x_8, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_38);
lean_dec(x_34);
x_60 = lean_box(0);
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_58, x_8, x_60, x_9, x_10, x_40);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_15 = x_62;
x_16 = x_63;
goto block_21;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_58);
x_64 = l_Lean_MessageData_ofName(x_58);
x_65 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16;
lean_inc(x_64);
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_64);
lean_ctor_set(x_38, 0, x_65);
x_66 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_38);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MessageData_ofName(x_34);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = 1;
x_76 = 0;
lean_inc(x_9);
x_77 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_31, x_74, x_75, x_76, x_9, x_10, x_40);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_58, x_8, x_78, x_9, x_10, x_79);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_15 = x_81;
x_16 = x_82;
goto block_21;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_38);
lean_dec(x_34);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
lean_dec(x_56);
x_84 = lean_box(0);
x_85 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_83, x_8, x_84, x_9, x_10, x_40);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_15 = x_86;
x_16 = x_87;
goto block_21;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
lean_dec(x_38);
x_89 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_34);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_33);
x_90 = 0;
lean_inc(x_1);
x_91 = l_Lean_MessageData_ofConstName(x_1, x_90);
x_92 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__10;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__12;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_MessageData_ofName(x_34);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__14;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = 1;
lean_inc(x_9);
x_101 = l_Lean_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_31, x_99, x_100, x_90, x_9, x_10, x_88);
lean_dec(x_31);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_8);
x_15 = x_103;
x_16 = x_102;
goto block_21;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_89, 0);
lean_inc(x_104);
lean_dec(x_89);
x_105 = lean_ctor_get_uint8(x_104, sizeof(void*)*2);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_NameMap_contains___rarg(x_8, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_34);
x_108 = lean_box(0);
x_109 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_106, x_8, x_108, x_9, x_10, x_88);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_15 = x_110;
x_16 = x_111;
goto block_21;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_106);
x_112 = l_Lean_MessageData_ofName(x_106);
x_113 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16;
lean_inc(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_MessageData_ofName(x_34);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_112);
x_122 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = 1;
x_125 = 0;
lean_inc(x_9);
x_126 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_31, x_123, x_124, x_125, x_9, x_10, x_88);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_106, x_8, x_127, x_9, x_10, x_128);
lean_dec(x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_15 = x_130;
x_16 = x_131;
goto block_21;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_34);
x_132 = lean_ctor_get(x_104, 1);
lean_inc(x_132);
lean_dec(x_104);
x_133 = lean_box(0);
x_134 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_31, x_33, x_132, x_8, x_133, x_9, x_10, x_88);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_15 = x_135;
x_16 = x_136;
goto block_21;
}
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
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_array_size(x_3);
x_10 = 0;
lean_inc(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(x_1, x_2, x_3, x_8, x_3, x_9, x_10, x_7, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lake_DSL_expandAttrs___closed__1;
x_16 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4(x_15, x_12, x_4, x_5, x_13);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lake_DSL_mkConfigFields___closed__2;
x_20 = l_Lean_Syntax_mkSep(x_18, x_19);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = lean_array_mk(x_21);
x_23 = lean_box(2);
x_24 = l_Lake_DSL_mkConfigFields___closed__1;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = l_Lake_DSL_mkConfigFields___closed__2;
x_29 = l_Lean_Syntax_mkSep(x_26, x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
x_31 = lean_array_mk(x_30);
x_32 = lean_box(2);
x_33 = l_Lake_DSL_mkConfigFields___closed__1;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
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
LEAN_EXPORT lean_object* l_Lake_DSL_mkConfigFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_DSL_mkConfigFields(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Syntax_getArgs(x_1);
x_14 = l_Lean_Syntax_getHeadInfo(x_2);
x_15 = l_Lean_Syntax_TSepArray_getElems___rarg(x_13);
lean_dec(x_13);
x_16 = l_Lake_DSL_elabConfig___lambda__1___closed__1;
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_19 = l_Lake_DSL_mkConfigFields(x_4, x_18, x_15, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Command_getRef(x_10, x_11, x_21);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_166; 
x_166 = lean_box(0);
x_24 = x_166;
goto block_165;
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_9);
if (x_167 == 0)
{
x_24 = x_9;
goto block_165;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_9, 0);
lean_inc(x_168);
lean_dec(x_9);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_24 = x_169;
goto block_165;
}
}
block_165:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_28 = l_Lean_mkOptionalNode(x_24);
lean_dec(x_24);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 0, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_mk(x_30);
x_32 = lean_box(2);
x_33 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
x_35 = 0;
x_36 = l_Lean_SourceInfo_fromRef(x_26, x_35);
lean_dec(x_26);
x_37 = l_Lean_Elab_Command_getCurrMacroScope(x_10, x_11, x_27);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = l_Lean_Elab_Command_getMainModule___rarg(x_11, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_46 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_36);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_47, 6);
lean_inc(x_36);
x_49 = l_Lean_Syntax_node6(x_36, x_48, x_47, x_47, x_47, x_47, x_47, x_47);
x_50 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_36);
lean_ctor_set_tag(x_41, 2);
lean_ctor_set(x_41, 1, x_50);
lean_ctor_set(x_41, 0, x_36);
x_51 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_51);
lean_ctor_set(x_37, 0, x_5);
x_52 = lean_array_mk(x_37);
x_53 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_52);
x_55 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_36);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_36);
x_58 = l_Lean_Syntax_node2(x_36, x_57, x_56, x_6);
lean_inc(x_36);
x_59 = l_Lean_Syntax_node1(x_36, x_45, x_58);
x_60 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_47);
lean_inc(x_36);
x_61 = l_Lean_Syntax_node2(x_36, x_60, x_47, x_59);
x_62 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_36);
x_63 = l_Lean_Syntax_node5(x_36, x_62, x_41, x_54, x_61, x_34, x_47);
x_64 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_65 = l_Lean_Syntax_node2(x_36, x_64, x_49, x_63);
lean_inc(x_65);
x_66 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_66, 0, x_65);
x_67 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_7, x_65, x_66, x_10, x_11, x_43);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_68 = lean_ctor_get(x_41, 1);
lean_inc(x_68);
lean_dec(x_41);
x_69 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_70 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_36);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_36);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_71, 6);
lean_inc(x_36);
x_73 = l_Lean_Syntax_node6(x_36, x_72, x_71, x_71, x_71, x_71, x_71, x_71);
x_74 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_36);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_36);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_76);
lean_ctor_set(x_37, 0, x_5);
x_77 = lean_array_mk(x_37);
x_78 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_77);
x_80 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_36);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_36);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_36);
x_83 = l_Lean_Syntax_node2(x_36, x_82, x_81, x_6);
lean_inc(x_36);
x_84 = l_Lean_Syntax_node1(x_36, x_69, x_83);
x_85 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_71);
lean_inc(x_36);
x_86 = l_Lean_Syntax_node2(x_36, x_85, x_71, x_84);
x_87 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_36);
x_88 = l_Lean_Syntax_node5(x_36, x_87, x_75, x_79, x_86, x_34, x_71);
x_89 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_90 = l_Lean_Syntax_node2(x_36, x_89, x_73, x_88);
lean_inc(x_90);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_91, 0, x_90);
x_92 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_7, x_90, x_91, x_10, x_11, x_68);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
lean_dec(x_37);
x_94 = l_Lean_Elab_Command_getMainModule___rarg(x_11, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_98 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_36);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_36);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_98);
x_100 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_99, 6);
lean_inc(x_36);
x_101 = l_Lean_Syntax_node6(x_36, x_100, x_99, x_99, x_99, x_99, x_99, x_99);
x_102 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_36);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(2, 2, 0);
} else {
 x_103 = x_96;
 lean_ctor_set_tag(x_103, 2);
}
lean_ctor_set(x_103, 0, x_36);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_5);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_mk(x_105);
x_107 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_32);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_106);
x_109 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_36);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_36);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_36);
x_112 = l_Lean_Syntax_node2(x_36, x_111, x_110, x_6);
lean_inc(x_36);
x_113 = l_Lean_Syntax_node1(x_36, x_97, x_112);
x_114 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_99);
lean_inc(x_36);
x_115 = l_Lean_Syntax_node2(x_36, x_114, x_99, x_113);
x_116 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_36);
x_117 = l_Lean_Syntax_node5(x_36, x_116, x_103, x_108, x_115, x_34, x_99);
x_118 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_119 = l_Lean_Syntax_node2(x_36, x_118, x_101, x_117);
lean_inc(x_119);
x_120 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_120, 0, x_119);
x_121 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_7, x_119, x_120, x_10, x_11, x_95);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_122 = lean_ctor_get(x_23, 0);
x_123 = lean_ctor_get(x_23, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_23);
x_124 = l_Lean_mkOptionalNode(x_24);
lean_dec(x_24);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_22);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_20);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_17);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_mk(x_127);
x_129 = lean_box(2);
x_130 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_128);
x_132 = 0;
x_133 = l_Lean_SourceInfo_fromRef(x_122, x_132);
lean_dec(x_122);
x_134 = l_Lean_Elab_Command_getCurrMacroScope(x_10, x_11, x_123);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = l_Lean_Elab_Command_getMainModule___rarg(x_11, x_135);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_141 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_133);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_133);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_142, 6);
lean_inc(x_133);
x_144 = l_Lean_Syntax_node6(x_133, x_143, x_142, x_142, x_142, x_142, x_142, x_142);
x_145 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_133);
if (lean_is_scalar(x_139)) {
 x_146 = lean_alloc_ctor(2, 2, 0);
} else {
 x_146 = x_139;
 lean_ctor_set_tag(x_146, 2);
}
lean_ctor_set(x_146, 0, x_133);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lake_DSL_elabConfig___lambda__1___closed__14;
if (lean_is_scalar(x_136)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_136;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_5);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_mk(x_148);
x_150 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_129);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_149);
x_152 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_133);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_133);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_133);
x_155 = l_Lean_Syntax_node2(x_133, x_154, x_153, x_6);
lean_inc(x_133);
x_156 = l_Lean_Syntax_node1(x_133, x_140, x_155);
x_157 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_142);
lean_inc(x_133);
x_158 = l_Lean_Syntax_node2(x_133, x_157, x_142, x_156);
x_159 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_133);
x_160 = l_Lean_Syntax_node5(x_133, x_159, x_146, x_151, x_158, x_131, x_142);
x_161 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_162 = l_Lean_Syntax_node2(x_133, x_161, x_144, x_160);
lean_inc(x_162);
x_163 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_163, 0, x_162);
x_164 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_7, x_162, x_163, x_10, x_11, x_138);
return x_164;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_170 = !lean_is_exclusive(x_19);
if (x_170 == 0)
{
return x_19;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_19, 0);
x_172 = lean_ctor_get(x_19, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_19);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
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
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_DSL_optConfig___closed__2;
lean_inc(x_5);
x_10 = l_Lean_Syntax_isOfKind(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lake_DSL_elabConfig___closed__2;
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_5, x_13);
lean_inc(x_14);
x_15 = l_Lean_Syntax_matchesNull(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_17 = l_Lean_Syntax_matchesNull(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = l_Lake_DSL_elabConfig___closed__2;
x_19 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_18, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
x_21 = l_Lake_DSL_declValWhere___closed__2;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lake_DSL_declValStruct___closed__2;
lean_inc(x_20);
x_24 = l_Lean_Syntax_isOfKind(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = l_Lake_DSL_elabConfig___closed__2;
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_25, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Syntax_getArg(x_20, x_13);
x_28 = l_Lake_DSL_structVal___closed__2;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = l_Lake_DSL_elabConfig___closed__2;
x_31 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_30, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Syntax_getArg(x_27, x_13);
x_33 = l_Lean_Syntax_getArg(x_27, x_16);
lean_dec(x_27);
x_34 = l_Lake_DSL_mkConfigFields___closed__1;
lean_inc(x_33);
x_35 = l_Lean_Syntax_isOfKind(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = l_Lake_DSL_elabConfig___closed__2;
x_37 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_36, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Syntax_getArg(x_33, x_13);
lean_dec(x_33);
x_39 = l_Lean_Syntax_getArg(x_20, x_16);
lean_dec(x_20);
x_40 = l_Lean_Syntax_isNone(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_inc(x_39);
x_41 = l_Lean_Syntax_matchesNull(x_39, x_16);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = l_Lake_DSL_elabConfig___closed__2;
x_43 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_42, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Syntax_getArg(x_39, x_13);
lean_dec(x_39);
x_45 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_44);
x_46 = l_Lean_Syntax_isOfKind(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = l_Lake_DSL_elabConfig___closed__2;
x_48 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_47, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_50 = lean_box(0);
x_51 = l_Lake_DSL_elabConfig___lambda__1(x_38, x_32, x_2, x_1, x_3, x_4, x_5, x_50, x_49, x_6, x_7, x_8);
lean_dec(x_32);
lean_dec(x_38);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_39);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = l_Lake_DSL_elabConfig___lambda__1(x_38, x_32, x_2, x_1, x_3, x_4, x_5, x_53, x_52, x_6, x_7, x_8);
lean_dec(x_32);
lean_dec(x_38);
return x_54;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArg(x_20, x_13);
x_56 = l_Lean_Syntax_getArg(x_20, x_16);
x_57 = l_Lake_DSL_mkConfigFields___closed__1;
lean_inc(x_56);
x_58 = l_Lean_Syntax_isOfKind(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = l_Lake_DSL_elabConfig___closed__2;
x_60 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_59, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = l_Lean_Syntax_getArg(x_56, x_13);
lean_dec(x_56);
x_62 = lean_unsigned_to_nat(2u);
x_63 = l_Lean_Syntax_getArg(x_20, x_62);
lean_dec(x_20);
x_64 = l_Lean_Syntax_isNone(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_inc(x_63);
x_65 = l_Lean_Syntax_matchesNull(x_63, x_16);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_55);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = l_Lake_DSL_elabConfig___closed__2;
x_67 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_66, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_Syntax_getArg(x_63, x_13);
lean_dec(x_63);
x_69 = l_Lake_DSL_declValDo___closed__13;
lean_inc(x_68);
x_70 = l_Lean_Syntax_isOfKind(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_61);
lean_dec(x_55);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = l_Lake_DSL_elabConfig___closed__2;
x_72 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabSyntax___spec__13(x_5, x_71, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_74 = lean_box(0);
x_75 = l_Lake_DSL_elabConfig___lambda__1(x_61, x_55, x_2, x_1, x_3, x_4, x_5, x_74, x_73, x_6, x_7, x_8);
lean_dec(x_55);
lean_dec(x_61);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_63);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = l_Lake_DSL_elabConfig___lambda__1(x_61, x_55, x_2, x_1, x_3, x_4, x_5, x_77, x_76, x_6, x_7, x_8);
lean_dec(x_55);
lean_dec(x_61);
return x_78;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_14);
x_79 = lean_ctor_get(x_2, 1);
x_80 = l_Lake_DSL_expandAttrs___closed__1;
lean_inc(x_6);
x_81 = l_Lake_DSL_mkConfigFields(x_1, x_79, x_80, x_6, x_7, x_8);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lake_DSL_elabConfig___closed__5;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lake_DSL_elabConfig___closed__3;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_mk(x_87);
x_89 = lean_box(2);
x_90 = l_Lake_DSL_elabConfig___lambda__1___closed__3;
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_88);
x_92 = l_Lean_Elab_Command_getRef(x_6, x_7, x_83);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = 0;
x_97 = l_Lean_SourceInfo_fromRef(x_94, x_96);
lean_dec(x_94);
x_98 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_95);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_98, 1);
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
x_102 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_100);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_104 = lean_ctor_get(x_102, 1);
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_107 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_97);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_108, 6);
lean_inc(x_97);
x_110 = l_Lean_Syntax_node6(x_97, x_109, x_108, x_108, x_108, x_108, x_108, x_108);
x_111 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_97);
lean_ctor_set_tag(x_102, 2);
lean_ctor_set(x_102, 1, x_111);
lean_ctor_set(x_102, 0, x_97);
x_112 = l_Lake_DSL_elabConfig___closed__7;
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_112);
lean_ctor_set(x_98, 0, x_3);
x_113 = lean_array_mk(x_98);
x_114 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_89);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_113);
x_116 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_97);
lean_ctor_set_tag(x_92, 2);
lean_ctor_set(x_92, 1, x_116);
lean_ctor_set(x_92, 0, x_97);
x_117 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_97);
x_118 = l_Lean_Syntax_node2(x_97, x_117, x_92, x_4);
lean_inc(x_97);
x_119 = l_Lean_Syntax_node1(x_97, x_106, x_118);
x_120 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_108);
lean_inc(x_97);
x_121 = l_Lean_Syntax_node2(x_97, x_120, x_108, x_119);
x_122 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_97);
x_123 = l_Lean_Syntax_node5(x_97, x_122, x_102, x_115, x_121, x_91, x_108);
x_124 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_125 = l_Lean_Syntax_node2(x_97, x_124, x_110, x_123);
lean_inc(x_125);
x_126 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_126, 0, x_125);
x_127 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_125, x_126, x_6, x_7, x_104);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_128 = lean_ctor_get(x_102, 1);
lean_inc(x_128);
lean_dec(x_102);
x_129 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_130 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_97);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_97);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_130);
x_132 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_131, 6);
lean_inc(x_97);
x_133 = l_Lean_Syntax_node6(x_97, x_132, x_131, x_131, x_131, x_131, x_131, x_131);
x_134 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_97);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_97);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lake_DSL_elabConfig___closed__7;
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_136);
lean_ctor_set(x_98, 0, x_3);
x_137 = lean_array_mk(x_98);
x_138 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_89);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
x_140 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_97);
lean_ctor_set_tag(x_92, 2);
lean_ctor_set(x_92, 1, x_140);
lean_ctor_set(x_92, 0, x_97);
x_141 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_97);
x_142 = l_Lean_Syntax_node2(x_97, x_141, x_92, x_4);
lean_inc(x_97);
x_143 = l_Lean_Syntax_node1(x_97, x_129, x_142);
x_144 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_131);
lean_inc(x_97);
x_145 = l_Lean_Syntax_node2(x_97, x_144, x_131, x_143);
x_146 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_97);
x_147 = l_Lean_Syntax_node5(x_97, x_146, x_135, x_139, x_145, x_91, x_131);
x_148 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_149 = l_Lean_Syntax_node2(x_97, x_148, x_133, x_147);
lean_inc(x_149);
x_150 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_149, x_150, x_6, x_7, x_128);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_152 = lean_ctor_get(x_98, 1);
lean_inc(x_152);
lean_dec(x_98);
x_153 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_152);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_157 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_97);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_97);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_157);
x_159 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_158, 6);
lean_inc(x_97);
x_160 = l_Lean_Syntax_node6(x_97, x_159, x_158, x_158, x_158, x_158, x_158, x_158);
x_161 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_97);
if (lean_is_scalar(x_155)) {
 x_162 = lean_alloc_ctor(2, 2, 0);
} else {
 x_162 = x_155;
 lean_ctor_set_tag(x_162, 2);
}
lean_ctor_set(x_162, 0, x_97);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lake_DSL_elabConfig___closed__7;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_3);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_mk(x_164);
x_166 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_89);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
x_168 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_97);
lean_ctor_set_tag(x_92, 2);
lean_ctor_set(x_92, 1, x_168);
lean_ctor_set(x_92, 0, x_97);
x_169 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_97);
x_170 = l_Lean_Syntax_node2(x_97, x_169, x_92, x_4);
lean_inc(x_97);
x_171 = l_Lean_Syntax_node1(x_97, x_156, x_170);
x_172 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_158);
lean_inc(x_97);
x_173 = l_Lean_Syntax_node2(x_97, x_172, x_158, x_171);
x_174 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_97);
x_175 = l_Lean_Syntax_node5(x_97, x_174, x_162, x_167, x_173, x_91, x_158);
x_176 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_177 = l_Lean_Syntax_node2(x_97, x_176, x_160, x_175);
lean_inc(x_177);
x_178 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_178, 0, x_177);
x_179 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_177, x_178, x_6, x_7, x_154);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_180 = lean_ctor_get(x_92, 0);
x_181 = lean_ctor_get(x_92, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_92);
x_182 = 0;
x_183 = l_Lean_SourceInfo_fromRef(x_180, x_182);
lean_dec(x_180);
x_184 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_181);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__8;
x_191 = l_Lean_RBNode_foldM___at_Lake_DSL_mkConfigFields___spec__4___closed__6;
lean_inc(x_183);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_190);
lean_ctor_set(x_192, 2, x_191);
x_193 = l_Lake_DSL_elabConfig___lambda__1___closed__7;
lean_inc_n(x_192, 6);
lean_inc(x_183);
x_194 = l_Lean_Syntax_node6(x_183, x_193, x_192, x_192, x_192, x_192, x_192, x_192);
x_195 = l_Lake_DSL_elabConfig___lambda__1___closed__10;
lean_inc(x_183);
if (lean_is_scalar(x_189)) {
 x_196 = lean_alloc_ctor(2, 2, 0);
} else {
 x_196 = x_189;
 lean_ctor_set_tag(x_196, 2);
}
lean_ctor_set(x_196, 0, x_183);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lake_DSL_elabConfig___closed__7;
if (lean_is_scalar(x_186)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_186;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_3);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_array_mk(x_198);
x_200 = l_Lake_DSL_elabConfig___lambda__1___closed__12;
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_89);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_199);
x_202 = l_Lake_DSL_expandOptSimpleBinder___lambda__1___closed__6;
lean_inc(x_183);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_183);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lake_DSL_simpleDeclSig___closed__4;
lean_inc(x_183);
x_205 = l_Lean_Syntax_node2(x_183, x_204, x_203, x_4);
lean_inc(x_183);
x_206 = l_Lean_Syntax_node1(x_183, x_190, x_205);
x_207 = l_Lake_DSL_elabConfig___lambda__1___closed__16;
lean_inc(x_192);
lean_inc(x_183);
x_208 = l_Lean_Syntax_node2(x_183, x_207, x_192, x_206);
x_209 = l_Lake_DSL_elabConfig___lambda__1___closed__9;
lean_inc(x_183);
x_210 = l_Lean_Syntax_node5(x_183, x_209, x_196, x_201, x_208, x_91, x_192);
x_211 = l_Lake_DSL_elabConfig___lambda__1___closed__5;
x_212 = l_Lean_Syntax_node2(x_183, x_211, x_194, x_210);
lean_inc(x_212);
x_213 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_213, 0, x_212);
x_214 = l_Lean_Elab_Command_withMacroExpansion___rarg(x_5, x_212, x_213, x_6, x_7, x_188);
return x_214;
}
}
else
{
uint8_t x_215; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_215 = !lean_is_exclusive(x_81);
if (x_215 == 0)
{
return x_81;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_81, 0);
x_217 = lean_ctor_get(x_81, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_81);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_DSL_elabConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_DSL_elabConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lake_DSL_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin, lean_object*);
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
res = initialize_Lake_Config_Meta(builtin, lean_io_mk_world());
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
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__15);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__16);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__17);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__18);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__19);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__20);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__21);
l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_DSL_mkConfigFields___spec__3___closed__22);
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
