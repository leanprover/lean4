// Lean compiler output
// Module: init.lean.elaborator.basic
// Imports: init.control.reader init.lean.namegenerator init.lean.scopes init.lean.parser.module
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
obj* l_Lean_checkSyntaxNodeKind___closed__1;
obj* l_Lean_mkMessage(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_getOpenDecls(obj*);
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2;
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_declareBuiltinCommandElab(obj*, obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_getNamespace___boxed(obj*);
obj* l_Lean_Elab_rootNamespace___closed__2;
extern obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
obj* l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(obj*, obj*, obj*);
obj* l_Lean_attrParamSyntaxToIdentifier(obj*);
obj* l_Lean_ElabScope_Inhabited;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elab_runIO___rarg(obj*);
extern "C" obj* lean_io_realpath(obj*, obj*);
obj* l_Lean_processCommandsAux___main___boxed(obj*);
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
obj* l_Lean_mkCommandElabAttribute___closed__1;
obj* l_Lean_Elab_Inhabited___boxed(obj*, obj*);
obj* l_Lean_Elab_runIOUnsafe(obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*, obj*);
obj* l_Lean_mkTermElabAttribute___closed__1;
obj* l_Lean_Elab_resolveNamespace___closed__1;
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___boxed(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__5;
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_logUnknownDecl___closed__1;
obj* l_Lean_mkElabAttribute___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinTermElab___closed__2;
obj* l_Lean_logUnknownDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_updateCmdPos___boxed(obj*);
extern obj* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
obj* l_Lean_processCommands(obj*, obj*);
extern obj* l_Lean_AttributeImpl_inhabited___closed__5;
obj* l_Lean_mkElabAttribute___at_Lean_mkCommandElabAttribute___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4(obj*, obj*);
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(obj*, obj*, obj*);
obj* l_Lean_Elab_runIO(obj*, obj*, obj*);
extern obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
uint8 l_Lean_Parser_isExitCommand(obj*);
obj* l_Lean_mkElabAttribute___rarg___lambda__2___boxed(obj*, obj*);
obj* l_Lean_runElab(obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1;
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1(obj*, obj*, obj*, uint8, obj*);
extern obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
obj* l_Lean_testFrontend___closed__3;
obj* l_Lean_addBuiltinTermElab___closed__2;
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
obj* l_Lean_registerBuiltinTermElabAttr___closed__7;
extern obj* l_Lean_Parser_Command_docComment___elambda__1___closed__2;
extern obj* l_Lean_findOLean___closed__1;
obj* l_Lean_termElabAttribute___closed__3;
obj* l_Lean_registerBuiltinTermElabAttr___closed__4;
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_Inhabited(obj*, obj*);
obj* l_Lean_logElabException(obj*, obj*, obj*);
namespace lean {
obj* import_modules_core(obj*, uint32, obj*);
}
obj* l_Lean_logError(obj*, obj*, obj*, obj*);
obj* l_List_reverse___rarg(obj*);
uint8 l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1(obj*, obj*);
uint8 l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(obj*, obj*);
obj* l_Lean_declareBuiltinTermElab___closed__1;
obj* l_Lean_mkTermElabAttribute___closed__2;
obj* l_Lean_mkElabAttribute___at_Lean_mkTermElabAttribute___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_addBuiltinCommandElab(obj*, obj*, obj*, obj*);
namespace lean {
obj* get_namespaces_core(obj*);
}
obj* l_Lean_processCommandsAux(obj*);
obj* l_Lean_Elab_removeRoot(obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Lean_processCommandsAux___main___rarg(obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_processCommandsAux___boxed(obj*);
obj* l_Lean_addRel___main(obj*, obj*);
extern obj* l_Lean_mkInitAttr___lambda__1___closed__1;
obj* l_AssocList_find___main___at_Lean_elabTerm___spec__3___boxed(obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___closed__2;
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___main(obj*, obj*, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___boxed(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3(obj*, obj*, obj*);
obj* l_Lean_syntaxNodeKindOfAttrParam___closed__1;
obj* l_Lean_Elab_resolveNamespaceUsingScopes(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_HashMapImp_find___at_Lean_elabTerm___spec__2(obj*, obj*);
obj* l_Lean_elabCommand(obj*, obj*, obj*);
obj* l_Lean_processHeader(obj*, obj*, obj*, obj*, uint32, obj*);
obj* l_Lean_addBuiltinCommandElab___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_depArrow___elambda__1___closed__4;
obj* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(obj*, obj*);
obj* l_Lean_OpenDecl_Inhabited___closed__1;
obj* l_Lean_toMessage___main(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinCommandElab___spec__11(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_elabCommand___spec__3___boxed(obj*, obj*);
extern "C" obj* lean_io_initializing(obj*);
obj* l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1(obj*, obj*);
obj* l_Lean_Elab_getScope(obj*);
obj* l_Lean_elabCommand___closed__2;
obj* l_Lean_elabCommand___closed__3;
namespace lean {
obj* mk_empty_environment_core(uint32, obj*);
}
obj* l_List_head___main___at_Lean_Elab_getScope___spec__1(obj*);
obj* l_Lean_termElabAttribute;
extern obj* l_Lean_AttributeImpl_inhabited___closed__4;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1;
obj* l_Lean_Elab_resolveNamespace(obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4;
obj* l_Lean_OpenDecl_HasToString(obj*);
extern obj* l_Lean_initAttr;
extern obj* l_Lean_Parser_declareBuiltinParser___closed__5;
obj* l_Lean_mkCommandElabAttribute___closed__2;
obj* l_Lean_Elab_resolveNamespaceUsingScopes___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2;
obj* l_RBNode_insert___at_Lean_addBuiltinCommandElab___spec__6(obj*, obj*, obj*);
obj* l_Lean_Elab_getNamespace___rarg(obj*);
obj* l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(obj*, obj*, obj*);
obj* l_Lean_Elab_runIO___boxed(obj*, obj*, obj*);
obj* l_Lean_commandElabAttribute;
obj* l_Lean_processCommand(obj*, obj*);
obj* l_Lean_elabTerm___closed__2;
obj* l_Lean_processHeader___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkBuiltinCommandElabTable(obj*);
obj* l_Lean_toMessage(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
extern obj* l_Lean_NameGenerator_Inhabited___closed__3;
obj* l_Lean_Elab_getNamespace(obj*);
extern "C" usize lean_name_hash_usize(obj*);
obj* l_Lean_elabCommandAtFrontend___boxed(obj*, obj*, obj*);
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
obj* l_Lean_PersistentEnvExtension_getState___rarg(obj*, obj*);
obj* l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr(obj*);
obj* l_Lean_logErrorAt___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_declareBuiltinElab___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Syntax_isNone___rarg(obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___closed__6;
obj* l_Lean_Syntax_getArg___rarg(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_HashMapImp_insert___at_Lean_addBuiltinCommandElab___spec__8(obj*, obj*, obj*);
obj* l_Lean_runElab___rarg(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(obj*, obj*);
obj* l_Lean_declareBuiltinElab___closed__3;
obj* l_Lean_toMessage___main___boxed(obj*, obj*, obj*);
obj* l_Lean_processHeaderAux___closed__2;
obj* l_Lean_logError___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___at_Lean_elabTerm___spec__3(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinCommandElab___closed__1;
obj* l_Lean_checkSyntaxNodeKind(obj*, obj*);
obj* l_Lean_runElab___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4___boxed(obj*, obj*);
obj* l_Lean_Elab_resolveNamespaceUsingScopes___boxed(obj*, obj*, obj*);
obj* l_Lean_updateCmdPos___rarg(obj*);
namespace lean {
obj* module_name_of_file_core(obj*, obj*);
}
extern obj* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
obj* l_Lean_Syntax_getArgs___rarg(obj*);
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___main___boxed(obj*, obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_logErrorAt(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_mkTermParserAttribute___closed__4;
obj* l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1___boxed(obj*, obj*);
obj* l_Lean_addBuiltinTermElab___closed__1;
obj* l_Lean_OpenDecl_HasToString___closed__1;
obj* l_Lean_addBuiltinTermElab(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_addBuiltinTermElab___spec__8(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1(obj*, obj*, obj*, uint8, obj*);
obj* l_System_FilePath_dirName(obj*);
obj* l_Lean_declareBuiltinCommandElab___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_processHeaderAux(obj*, obj*, uint32, obj*);
uint8 l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1(obj*, obj*);
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1;
obj* l_Lean_Elab_getUniverses___rarg(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_logElabException___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Elab_resolveNamespaceUsingScopes___main(obj*, obj*, obj*);
obj* l_Lean_nameToExprAux___main(obj*);
obj* l_Lean_ElabAttribute_Inhabited(obj*);
obj* l_List_head___main___at_Lean_Elab_getScope___spec__1___boxed(obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__6;
obj* l_Lean_Elab_getUniverses(obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
extern "C" obj* lean_add_and_compile(obj*, obj*, obj*);
obj* l_Lean_elabTerm___closed__3;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Syntax_getId___main___rarg(obj*);
uint8 l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(obj*, obj*);
obj* l_Lean_ElabException_Inhabited;
obj* l_Lean_getElabContext___boxed(obj*, obj*);
obj* l_Lean_getEnv___boxed(obj*);
extern obj* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
extern obj* l_Lean_AttributeImpl_inhabited___closed__1;
obj* l_Lean_elabTerm(obj*, obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
obj* l_mkHashMap___at_Lean_mkBuiltinCommandElabTable___spec__2(obj*);
obj* l_Array_push(obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_Elab_rootNamespace;
obj* l_Lean_logErrorAndThrow(obj*);
obj* l_Lean_declareBuiltinCommandElab___closed__2;
obj* l_Lean_getElabContext(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_elabCommand___spec__3(obj*, obj*);
obj* l_Lean_Syntax_asNode___main___rarg(obj*);
obj* l_Lean_mkBuiltinTermElabTable(obj*);
obj* l_Lean_logErrorUsingCmdPos(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___closed__5;
obj* l_Lean_getEnv___rarg(obj*);
obj* l_Lean_termElabAttribute___closed__2;
obj* l_Lean_modNameToFileName___main(obj*);
obj* l_Lean_syntaxNodeKindOfAttrParam(obj*, obj*, obj*, obj*);
obj* l_Lean_updateCmdPos(obj*);
obj* l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3___boxed(obj*, obj*);
obj* l_Lean_Elab_resolveNamespace___boxed(obj*, obj*, obj*);
extern obj* l___private_init_lean_path_1__pathSep___closed__1;
obj* l_Lean_ElabException_Inhabited___closed__1;
obj* l_mkHashMap___at_Lean_mkBuiltinTermElabTable___spec__2(obj*);
extern obj* l_Lean_Parser_mkCommandParserAttribute___closed__4;
obj* l_Lean_elabCommandAtFrontend(obj*, obj*, obj*);
obj* l_Lean_Elab_getOpenDecls___boxed(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_runElab___at_Lean_processCommand___spec__1(obj*, obj*, obj*);
obj* l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_isNamespace(obj*, obj*);
obj* l_Lean_mkCApp(obj*, obj*);
obj* l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(obj*, obj*, obj*);
obj* l_Lean_testFrontend___closed__2;
obj* l_Lean_getEnv(obj*);
namespace lean {
obj* absolutize_module_name_core(obj*, obj*, obj*, obj*);
}
obj* l_Lean_Parser_parseCommand___main(obj*, obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__2(obj*, obj*);
obj* l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1(obj*, obj*);
obj* l_Lean_testFrontend(obj*, obj*, obj*);
uint8 l_Lean_Parser_isEOI(obj*);
obj* l_Lean_mkElabAttribute(obj*);
obj* l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2___boxed(obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
obj* l_Lean_mkCommandElabAttribute(obj*);
obj* l_Lean_syntaxNodeKindOfAttrParam___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_addBuiltinCommandElab___spec__9(obj*, obj*);
obj* l_Lean_absolutizeModuleName___closed__1;
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4(obj*, obj*);
obj* l_Lean_Elab_getUniverses___boxed(obj*);
obj* l_EState_bind___rarg(obj*, obj*, obj*);
obj* l_Lean_processCommandsAux___main(obj*);
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls(obj*, obj*, obj*);
obj* l_Lean_getPos___boxed(obj*, obj*, obj*);
uint8 l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2(obj*, obj*);
obj* l_Lean_OpenDecl_Inhabited;
obj* l_Lean_mkElabAttribute___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_addBuiltinTermElab___spec__9(obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5;
obj* l_Lean_registerBuiltinCommandElabAttr___closed__4;
obj* l_Lean_declareBuiltinElab___closed__2;
obj* l_Lean_mkMessage___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
obj* l_Lean_ElabException_Inhabited___closed__2;
extern obj* l_System_FilePath_dirName___closed__1;
obj* l_Lean_processHeaderAux___closed__1;
obj* l_Lean_logErrorUsingCmdPos___boxed(obj*, obj*, obj*);
obj* l_Lean_checkSyntaxNodeKindAtNamespaces(obj*, obj*, obj*);
obj* l_Lean_Parser_mkParserContextCore(obj*, obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
obj* l_Lean_elabCommand___closed__1;
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinTermElab___spec__11(obj*, obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg___boxed(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1;
obj* l_Lean_elabTerm___closed__1;
obj* l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(obj*, obj*, obj*);
obj* l_Lean_runElab___at_Lean_processCommand___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Lean_ParametricAttribute_setParam___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
extern obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
obj* l_Lean_ConstantInfo_type(obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_registerBuiltinTermElabAttr___closed__2;
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinTermElab___spec__10(obj*, obj*, obj*);
extern obj* l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4___boxed(obj*, obj*);
obj* l_HashMapImp_find___at_Lean_elabCommand___spec__2___boxed(obj*, obj*);
extern obj* l_Lean_AttributeImpl_inhabited___closed__6;
obj* l_Lean_processCommandsAux___rarg(obj*, obj*);
obj* l_Lean_logErrorAndThrow___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_addBuiltinCommandElab___closed__1;
obj* l_Lean_logUnknownDecl(obj*, obj*, obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_Elab_getOpenDecls___rarg(obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
obj* l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1___boxed(obj*, obj*);
obj* l_Lean_testFrontend___closed__1;
obj* l_Array_size(obj*, obj*);
obj* l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinTermElab___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___closed__3;
obj* l_Lean_declareBuiltinTermElab(obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_str2ElabException(obj*);
obj* l_mkHashMapImp___rarg(obj*);
uint8 l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2(obj*, obj*);
obj* l_Lean_getPos(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__1;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1;
obj* l_Lean_syntaxNodeKindOfAttrParam___closed__2;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1;
obj* l_Lean_mkElabAttribute___rarg___lambda__2(obj*, obj*);
obj* l_Lean_addBuiltinTermElab___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_elabTerm___spec__2___boxed(obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__2(obj*, obj*);
obj* l_Lean_builtinCommandElabTable;
extern obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern obj* l_Lean_nameToExprAux___main___closed__4;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
extern obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
obj* l_Lean_ElabAttribute_Inhabited___rarg(obj*);
obj* l_Lean_Elab_getScope___boxed(obj*);
obj* l_Lean_toBaseDir(obj*, obj*);
obj* l_Lean_Syntax_getPos___rarg(obj*);
obj* l_Lean_ElabScope_Inhabited___closed__1;
obj* l_Lean_mkElabAttribute___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_declareBuiltinElab___closed__1;
obj* l_Lean_registerBuiltinCommandElabAttr___closed__7;
obj* l_Lean_termElabAttribute___closed__1;
obj* l_Lean_Elab_getScope___rarg(obj*);
obj* l_RBNode_insert___at_Lean_addBuiltinTermElab___spec__6(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4;
obj* l_Lean_mkElabAttribute___rarg___lambda__2___closed__1;
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__3;
obj* l_Lean_processHeaderAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinCommandElabAttr(obj*);
obj* l_Lean_registerBuiltinCommandElabAttr___closed__1;
obj* l_Lean_declareBuiltinElab(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_Inhabited___rarg(obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getNumArgs___rarg(obj*);
obj* l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_registerPersistentEnvExtensionUnsafe___rarg(obj*, obj*, obj*);
extern obj* l___private_init_lean_environment_8__persistentEnvExtensionsRef;
obj* l_Lean_toMessage___boxed(obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(obj*, obj*, obj*);
obj* l_HashMapImp_find___at_Lean_elabCommand___spec__2(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinCommandElab___spec__10(obj*, obj*, obj*);
extern obj* l_Lean_mkInitAttr___closed__2;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2___boxed(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_mkElabAttribute___rarg___closed__1;
obj* l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3___boxed(obj*, obj*);
obj* l_Lean_mkTermElabAttribute(obj*);
extern obj* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
obj* l_IO_Prim_Ref_reset(obj*, obj*, obj*);
obj* l_Lean_Elab_rootNamespace___closed__1;
obj* l_Lean_testFrontend___closed__4;
extern obj* l___private_init_lean_environment_5__envExtensionsRef;
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_builtinTermElabTable;
obj* l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_isValidSyntaxNodeKind(obj*, obj*);
obj* l_Lean_logErrorAndThrow___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_parseHeader(obj*, obj*);
obj* l_List_toString___main___at_Lean_Environment_displayStats___spec__1(obj*);
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__4(obj*, obj*);
obj* _init_l_Lean_OpenDecl_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_OpenDecl_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_OpenDecl_Inhabited___closed__1;
return x_1;
}
}
obj* _init_l_Lean_OpenDecl_HasToString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" hiding ");
return x_1;
}
}
obj* l_Lean_OpenDecl_HasToString(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
return x_4;
}
case 1:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_5);
x_9 = l_Lean_Parser_Term_depArrow___elambda__1___closed__4;
x_10 = lean::string_append(x_8, x_9);
x_11 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_12 = lean::string_append(x_10, x_11);
lean::dec(x_11);
return x_12;
}
default: 
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = l_Lean_OpenDecl_HasToString___closed__1;
x_18 = lean::string_append(x_16, x_17);
x_19 = l_List_toString___main___at_Lean_Environment_displayStats___spec__1(x_14);
x_20 = lean::string_append(x_18, x_19);
lean::dec(x_19);
return x_20;
}
}
}
}
obj* _init_l_Lean_ElabScope_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean::box(0);
x_4 = l_Lean_Options_empty;
x_5 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set(x_5, 4, x_1);
lean::cnstr_set(x_5, 5, x_1);
return x_5;
}
}
obj* _init_l_Lean_ElabScope_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ElabScope_Inhabited___closed__1;
return x_1;
}
}
obj* _init_l_Lean_ElabException_Inhabited___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("error");
return x_1;
}
}
obj* _init_l_Lean_ElabException_Inhabited___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_ElabException_Inhabited___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_ElabException_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ElabException_Inhabited___closed__2;
return x_1;
}
}
obj* l_Lean_str2ElabException(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_mkHashMap___at_Lean_mkBuiltinTermElabTable___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1() {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2;
return x_1;
}
}
obj* l_Lean_mkBuiltinTermElabTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_mkHashMap___at_Lean_mkBuiltinCommandElabTable___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1() {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2;
return x_1;
}
}
obj* l_Lean_mkBuiltinCommandElabTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8 l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(obj* x_1, obj* x_2) {
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
uint8 l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2(obj* x_1, obj* x_2) {
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
x_10 = l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
uint8 l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2(x_4, x_2);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
lean::dec(x_7);
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2(x_11, x_2);
return x_12;
}
}
}
obj* l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_addBuiltinTermElab___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_addBuiltinTermElab___spec__7(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinTermElab___spec__11(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinTermElab___spec__10(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_mfoldl___main___at_Lean_addBuiltinTermElab___spec__11(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_addBuiltinTermElab___spec__9(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_addBuiltinTermElab___spec__10(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_addBuiltinTermElab___spec__8(obj* x_1, obj* x_2, obj* x_3) {
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
x_13 = l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_addBuiltinTermElab___spec__9(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(x_2, x_3, x_12);
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
x_32 = l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_addBuiltinTermElab___spec__9(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_addBuiltinTermElab___spec__12(x_2, x_3, x_31);
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
obj* l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_addBuiltinTermElab___spec__6(x_6, x_2, x_3);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_RBNode_insert___at_Lean_addBuiltinTermElab___spec__6(x_9, x_2, x_3);
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_addBuiltinTermElab___spec__8(x_13, x_2, x_3);
lean::cnstr_set(x_1, 0, x_14);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_addBuiltinTermElab___spec__8(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
obj* _init_l_Lean_addBuiltinTermElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid builtin term elaborator, elaborator for '");
return x_1;
}
}
obj* _init_l_Lean_addBuiltinTermElab___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' has already been defined");
return x_1;
}
}
obj* l_Lean_addBuiltinTermElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_builtinTermElabTable;
x_6 = lean::io_ref_get(x_5, x_4);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1(x_8, x_1);
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
x_17 = l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(x_13, x_1, x_3);
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
x_21 = l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(x_13, x_1, x_3);
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
x_34 = l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(x_27, x_1, x_3);
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
x_52 = l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1(x_50, x_1);
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
x_64 = l_Lean_SMap_insert___main___at_Lean_addBuiltinTermElab___spec__5(x_56, x_1, x_3);
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
obj* l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_addBuiltinTermElab___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_addBuiltinTermElab___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_SMap_contains___main___at_Lean_addBuiltinTermElab___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_addBuiltinTermElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_addBuiltinTermElab(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
uint8 l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(obj* x_1, obj* x_2) {
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
uint8 l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2(obj* x_1, obj* x_2) {
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
x_10 = l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
uint8 l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2(x_4, x_2);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
lean::dec(x_7);
x_9 = 1;
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2(x_11, x_2);
return x_12;
}
}
}
obj* l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 3);
x_12 = l_Lean_Name_quickLt(x_2, x_9);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Lean_Name_quickLt(x_9, x_2);
if (x_13 == 0)
{
lean::dec(x_10);
lean::dec(x_9);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_14; 
x_14 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_11, x_2, x_3);
lean::cnstr_set(x_1, 3, x_14);
return x_1;
}
}
else
{
obj* x_15; 
x_15 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_8, x_2, x_3);
lean::cnstr_set(x_1, 0, x_15);
return x_1;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_16 = lean::cnstr_get(x_1, 0);
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_1);
x_20 = l_Lean_Name_quickLt(x_2, x_17);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Lean_Name_quickLt(x_17, x_2);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_18);
lean::dec(x_17);
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_3);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_19, x_2, x_3);
x_24 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_18);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
else
{
obj* x_25; obj* x_26; 
x_25 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_16, x_2, x_3);
x_26 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
return x_26;
}
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_28 = lean::cnstr_get(x_1, 0);
x_29 = lean::cnstr_get(x_1, 1);
x_30 = lean::cnstr_get(x_1, 2);
x_31 = lean::cnstr_get(x_1, 3);
x_32 = l_Lean_Name_quickLt(x_2, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = l_Lean_Name_quickLt(x_29, x_2);
if (x_33 == 0)
{
lean::dec(x_30);
lean::dec(x_29);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8 x_34; 
x_34 = l_RBNode_isRed___main___rarg(x_31);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_31, x_2, x_3);
lean::cnstr_set(x_1, 3, x_35);
return x_1;
}
else
{
obj* x_36; 
x_36 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_31, x_2, x_3);
if (lean::obj_tag(x_36) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
return x_36;
}
else
{
obj* x_37; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; 
x_38 = lean::cnstr_get(x_36, 3);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_36);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_36, 3);
lean::dec(x_40);
x_41 = lean::cnstr_get(x_36, 0);
lean::dec(x_41);
x_42 = 0;
lean::cnstr_set(x_36, 0, x_38);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_42);
x_43 = 1;
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_36, 1);
x_45 = lean::cnstr_get(x_36, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_36);
x_46 = 0;
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_38);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
lean::cnstr_set(x_47, 3, x_38);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_46);
x_48 = 1;
lean::cnstr_set(x_1, 3, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_36);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_36, 1);
x_52 = lean::cnstr_get(x_36, 2);
x_53 = lean::cnstr_get(x_36, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_36, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_38);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_38, 0);
x_57 = lean::cnstr_get(x_38, 1);
x_58 = lean::cnstr_get(x_38, 2);
x_59 = lean::cnstr_get(x_38, 3);
x_60 = 1;
lean::cnstr_set(x_38, 3, x_37);
lean::cnstr_set(x_38, 2, x_30);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_60);
lean::cnstr_set(x_36, 3, x_59);
lean::cnstr_set(x_36, 2, x_58);
lean::cnstr_set(x_36, 1, x_57);
lean::cnstr_set(x_36, 0, x_56);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_60);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_38);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_38, 0);
x_62 = lean::cnstr_get(x_38, 1);
x_63 = lean::cnstr_get(x_38, 2);
x_64 = lean::cnstr_get(x_38, 3);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_38);
x_65 = 1;
x_66 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_66, 0, x_28);
lean::cnstr_set(x_66, 1, x_29);
lean::cnstr_set(x_66, 2, x_30);
lean::cnstr_set(x_66, 3, x_37);
lean::cnstr_set_scalar(x_66, sizeof(void*)*4, x_65);
lean::cnstr_set(x_36, 3, x_64);
lean::cnstr_set(x_36, 2, x_63);
lean::cnstr_set(x_36, 1, x_62);
lean::cnstr_set(x_36, 0, x_61);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_65);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_52);
lean::cnstr_set(x_1, 1, x_51);
lean::cnstr_set(x_1, 0, x_66);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_36, 1);
x_68 = lean::cnstr_get(x_36, 2);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_36);
x_69 = lean::cnstr_get(x_38, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_38, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_38, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_38, 3);
lean::inc(x_72);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 x_73 = x_38;
} else {
 lean::dec_ref(x_38);
 x_73 = lean::box(0);
}
x_74 = 1;
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_28);
lean::cnstr_set(x_75, 1, x_29);
lean::cnstr_set(x_75, 2, x_30);
lean::cnstr_set(x_75, 3, x_37);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_69);
lean::cnstr_set(x_76, 1, x_70);
lean::cnstr_set(x_76, 2, x_71);
lean::cnstr_set(x_76, 3, x_72);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_76);
lean::cnstr_set(x_1, 2, x_68);
lean::cnstr_set(x_1, 1, x_67);
lean::cnstr_set(x_1, 0, x_75);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_36);
if (x_77 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; 
x_78 = lean::cnstr_get(x_36, 3);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_36, 0);
lean::dec(x_79);
x_80 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_80);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
else
{
obj* x_81; obj* x_82; uint8 x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_36, 1);
x_82 = lean::cnstr_get(x_36, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_36);
x_83 = 0;
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_37);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
lean::cnstr_set(x_84, 3, x_38);
lean::cnstr_set_scalar(x_84, sizeof(void*)*4, x_83);
lean::cnstr_set(x_1, 3, x_84);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
}
}
else
{
uint8 x_85; 
x_85 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*4);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_36);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_36, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_37);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_37, 0);
x_90 = lean::cnstr_get(x_37, 1);
x_91 = lean::cnstr_get(x_37, 2);
x_92 = lean::cnstr_get(x_37, 3);
x_93 = 1;
lean::cnstr_set(x_37, 3, x_89);
lean::cnstr_set(x_37, 2, x_30);
lean::cnstr_set(x_37, 1, x_29);
lean::cnstr_set(x_37, 0, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_93);
lean::cnstr_set(x_36, 0, x_92);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_91);
lean::cnstr_set(x_1, 1, x_90);
lean::cnstr_set(x_1, 0, x_37);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; 
x_94 = lean::cnstr_get(x_37, 0);
x_95 = lean::cnstr_get(x_37, 1);
x_96 = lean::cnstr_get(x_37, 2);
x_97 = lean::cnstr_get(x_37, 3);
lean::inc(x_97);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_37);
x_98 = 1;
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_28);
lean::cnstr_set(x_99, 1, x_29);
lean::cnstr_set(x_99, 2, x_30);
lean::cnstr_set(x_99, 3, x_94);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_98);
lean::cnstr_set(x_36, 0, x_97);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_98);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set(x_1, 2, x_96);
lean::cnstr_set(x_1, 1, x_95);
lean::cnstr_set(x_1, 0, x_99);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
x_100 = lean::cnstr_get(x_36, 1);
x_101 = lean::cnstr_get(x_36, 2);
x_102 = lean::cnstr_get(x_36, 3);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_36);
x_103 = lean::cnstr_get(x_37, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_37, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_37, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_37, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_107 = x_37;
} else {
 lean::dec_ref(x_37);
 x_107 = lean::box(0);
}
x_108 = 1;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_28);
lean::cnstr_set(x_109, 1, x_29);
lean::cnstr_set(x_109, 2, x_30);
lean::cnstr_set(x_109, 3, x_103);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
x_110 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_100);
lean::cnstr_set(x_110, 2, x_101);
lean::cnstr_set(x_110, 3, x_102);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_110);
lean::cnstr_set(x_1, 2, x_105);
lean::cnstr_set(x_1, 1, x_104);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
obj* x_111; 
x_111 = lean::cnstr_get(x_36, 3);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_36);
if (x_112 == 0)
{
obj* x_113; obj* x_114; uint8 x_115; 
x_113 = lean::cnstr_get(x_36, 3);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_36, 0);
lean::dec(x_114);
x_115 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_115);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
else
{
obj* x_116; obj* x_117; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_36, 1);
x_117 = lean::cnstr_get(x_36, 2);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_36);
x_118 = 0;
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_37);
lean::cnstr_set(x_119, 1, x_116);
lean::cnstr_set(x_119, 2, x_117);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_85);
return x_1;
}
}
else
{
uint8 x_120; 
x_120 = lean::cnstr_get_scalar<uint8>(x_111, sizeof(void*)*4);
if (x_120 == 0)
{
uint8 x_121; 
lean::free_heap_obj(x_1);
x_121 = !lean::is_exclusive(x_36);
if (x_121 == 0)
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_36, 3);
lean::dec(x_122);
x_123 = lean::cnstr_get(x_36, 0);
lean::dec(x_123);
x_124 = !lean::is_exclusive(x_111);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; 
x_125 = lean::cnstr_get(x_111, 0);
x_126 = lean::cnstr_get(x_111, 1);
x_127 = lean::cnstr_get(x_111, 2);
x_128 = lean::cnstr_get(x_111, 3);
lean::inc(x_37);
lean::cnstr_set(x_111, 3, x_37);
lean::cnstr_set(x_111, 2, x_30);
lean::cnstr_set(x_111, 1, x_29);
lean::cnstr_set(x_111, 0, x_28);
x_129 = !lean::is_exclusive(x_37);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_37, 3);
lean::dec(x_130);
x_131 = lean::cnstr_get(x_37, 2);
lean::dec(x_131);
x_132 = lean::cnstr_get(x_37, 1);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_37, 0);
lean::dec(x_133);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
lean::cnstr_set(x_37, 3, x_128);
lean::cnstr_set(x_37, 2, x_127);
lean::cnstr_set(x_37, 1, x_126);
lean::cnstr_set(x_37, 0, x_125);
lean::cnstr_set(x_36, 3, x_37);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
else
{
obj* x_134; 
lean::dec(x_37);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_85);
x_134 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_134, 0, x_125);
lean::cnstr_set(x_134, 1, x_126);
lean::cnstr_set(x_134, 2, x_127);
lean::cnstr_set(x_134, 3, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_134);
lean::cnstr_set(x_36, 0, x_111);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_135 = lean::cnstr_get(x_111, 0);
x_136 = lean::cnstr_get(x_111, 1);
x_137 = lean::cnstr_get(x_111, 2);
x_138 = lean::cnstr_get(x_111, 3);
lean::inc(x_138);
lean::inc(x_137);
lean::inc(x_136);
lean::inc(x_135);
lean::dec(x_111);
lean::inc(x_37);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_28);
lean::cnstr_set(x_139, 1, x_29);
lean::cnstr_set(x_139, 2, x_30);
lean::cnstr_set(x_139, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_140 = x_37;
} else {
 lean::dec_ref(x_37);
 x_140 = lean::box(0);
}
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_135);
lean::cnstr_set(x_141, 1, x_136);
lean::cnstr_set(x_141, 2, x_137);
lean::cnstr_set(x_141, 3, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_85);
lean::cnstr_set(x_36, 3, x_141);
lean::cnstr_set(x_36, 0, x_139);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_120);
return x_36;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_142 = lean::cnstr_get(x_36, 1);
x_143 = lean::cnstr_get(x_36, 2);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_36);
x_144 = lean::cnstr_get(x_111, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_111, 1);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_111, 2);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_111, 3);
lean::inc(x_147);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 lean::cnstr_release(x_111, 2);
 lean::cnstr_release(x_111, 3);
 x_148 = x_111;
} else {
 lean::dec_ref(x_111);
 x_148 = lean::box(0);
}
lean::inc(x_37);
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_28);
lean::cnstr_set(x_149, 1, x_29);
lean::cnstr_set(x_149, 2, x_30);
lean::cnstr_set(x_149, 3, x_37);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_150 = x_37;
} else {
 lean::dec_ref(x_37);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_85);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_144);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_146);
lean::cnstr_set(x_151, 3, x_147);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_85);
x_152 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_142);
lean::cnstr_set(x_152, 2, x_143);
lean::cnstr_set(x_152, 3, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_120);
return x_152;
}
}
else
{
uint8 x_153; 
x_153 = !lean::is_exclusive(x_36);
if (x_153 == 0)
{
obj* x_154; obj* x_155; uint8 x_156; 
x_154 = lean::cnstr_get(x_36, 3);
lean::dec(x_154);
x_155 = lean::cnstr_get(x_36, 0);
lean::dec(x_155);
x_156 = !lean::is_exclusive(x_37);
if (x_156 == 0)
{
uint8 x_157; 
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_120);
x_157 = 0;
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_157);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; uint8 x_163; 
x_158 = lean::cnstr_get(x_37, 0);
x_159 = lean::cnstr_get(x_37, 1);
x_160 = lean::cnstr_get(x_37, 2);
x_161 = lean::cnstr_get(x_37, 3);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::dec(x_37);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set(x_162, 2, x_160);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_120);
x_163 = 0;
lean::cnstr_set(x_36, 0, x_162);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_163);
lean::cnstr_set(x_1, 3, x_36);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; uint8 x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_36, 1);
x_165 = lean::cnstr_get(x_36, 2);
lean::inc(x_165);
lean::inc(x_164);
lean::dec(x_36);
x_166 = lean::cnstr_get(x_37, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_37, 1);
lean::inc(x_167);
x_168 = lean::cnstr_get(x_37, 2);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_37, 3);
lean::inc(x_169);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 x_170 = x_37;
} else {
 lean::dec_ref(x_37);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_166);
lean::cnstr_set(x_171, 1, x_167);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*4, x_120);
x_172 = 0;
x_173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_164);
lean::cnstr_set(x_173, 2, x_165);
lean::cnstr_set(x_173, 3, x_111);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_172);
lean::cnstr_set(x_1, 3, x_173);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_174; 
x_174 = l_RBNode_isRed___main___rarg(x_28);
if (x_174 == 0)
{
obj* x_175; 
x_175 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_28, x_2, x_3);
lean::cnstr_set(x_1, 0, x_175);
return x_1;
}
else
{
obj* x_176; 
x_176 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_28, x_2, x_3);
if (lean::obj_tag(x_176) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_31);
lean::dec(x_30);
lean::dec(x_29);
return x_176;
}
else
{
obj* x_177; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_178; 
x_178 = lean::cnstr_get(x_176, 3);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_176);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; uint8 x_183; 
x_180 = lean::cnstr_get(x_176, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_176, 0);
lean::dec(x_181);
x_182 = 0;
lean::cnstr_set(x_176, 0, x_178);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_182);
x_183 = 1;
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
obj* x_184; obj* x_185; uint8 x_186; obj* x_187; uint8 x_188; 
x_184 = lean::cnstr_get(x_176, 1);
x_185 = lean::cnstr_get(x_176, 2);
lean::inc(x_185);
lean::inc(x_184);
lean::dec(x_176);
x_186 = 0;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_178);
lean::cnstr_set(x_187, 1, x_184);
lean::cnstr_set(x_187, 2, x_185);
lean::cnstr_set(x_187, 3, x_178);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = 1;
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_178, sizeof(void*)*4);
if (x_189 == 0)
{
uint8 x_190; 
x_190 = !lean::is_exclusive(x_176);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_176, 1);
x_192 = lean::cnstr_get(x_176, 2);
x_193 = lean::cnstr_get(x_176, 3);
lean::dec(x_193);
x_194 = lean::cnstr_get(x_176, 0);
lean::dec(x_194);
x_195 = !lean::is_exclusive(x_178);
if (x_195 == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; 
x_196 = lean::cnstr_get(x_178, 0);
x_197 = lean::cnstr_get(x_178, 1);
x_198 = lean::cnstr_get(x_178, 2);
x_199 = lean::cnstr_get(x_178, 3);
x_200 = 1;
lean::cnstr_set(x_178, 3, x_196);
lean::cnstr_set(x_178, 2, x_192);
lean::cnstr_set(x_178, 1, x_191);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_200);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_199);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_200);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_198);
lean::cnstr_set(x_1, 1, x_197);
lean::cnstr_set(x_1, 0, x_178);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; obj* x_206; 
x_201 = lean::cnstr_get(x_178, 0);
x_202 = lean::cnstr_get(x_178, 1);
x_203 = lean::cnstr_get(x_178, 2);
x_204 = lean::cnstr_get(x_178, 3);
lean::inc(x_204);
lean::inc(x_203);
lean::inc(x_202);
lean::inc(x_201);
lean::dec(x_178);
x_205 = 1;
x_206 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_206, 0, x_177);
lean::cnstr_set(x_206, 1, x_191);
lean::cnstr_set(x_206, 2, x_192);
lean::cnstr_set(x_206, 3, x_201);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_205);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_204);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_205);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_203);
lean::cnstr_set(x_1, 1, x_202);
lean::cnstr_set(x_1, 0, x_206);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; uint8 x_214; obj* x_215; obj* x_216; 
x_207 = lean::cnstr_get(x_176, 1);
x_208 = lean::cnstr_get(x_176, 2);
lean::inc(x_208);
lean::inc(x_207);
lean::dec(x_176);
x_209 = lean::cnstr_get(x_178, 0);
lean::inc(x_209);
x_210 = lean::cnstr_get(x_178, 1);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_178, 2);
lean::inc(x_211);
x_212 = lean::cnstr_get(x_178, 3);
lean::inc(x_212);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 lean::cnstr_release(x_178, 2);
 lean::cnstr_release(x_178, 3);
 x_213 = x_178;
} else {
 lean::dec_ref(x_178);
 x_213 = lean::box(0);
}
x_214 = 1;
if (lean::is_scalar(x_213)) {
 x_215 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_215 = x_213;
}
lean::cnstr_set(x_215, 0, x_177);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_208);
lean::cnstr_set(x_215, 3, x_209);
lean::cnstr_set_scalar(x_215, sizeof(void*)*4, x_214);
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_212);
lean::cnstr_set(x_216, 1, x_29);
lean::cnstr_set(x_216, 2, x_30);
lean::cnstr_set(x_216, 3, x_31);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_214);
lean::cnstr_set(x_1, 3, x_216);
lean::cnstr_set(x_1, 2, x_211);
lean::cnstr_set(x_1, 1, x_210);
lean::cnstr_set(x_1, 0, x_215);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
uint8 x_217; 
x_217 = !lean::is_exclusive(x_176);
if (x_217 == 0)
{
obj* x_218; obj* x_219; uint8 x_220; 
x_218 = lean::cnstr_get(x_176, 3);
lean::dec(x_218);
x_219 = lean::cnstr_get(x_176, 0);
lean::dec(x_219);
x_220 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_220);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
else
{
obj* x_221; obj* x_222; uint8 x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_176, 1);
x_222 = lean::cnstr_get(x_176, 2);
lean::inc(x_222);
lean::inc(x_221);
lean::dec(x_176);
x_223 = 0;
x_224 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_224, 0, x_177);
lean::cnstr_set(x_224, 1, x_221);
lean::cnstr_set(x_224, 2, x_222);
lean::cnstr_set(x_224, 3, x_178);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_223);
lean::cnstr_set(x_1, 0, x_224);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
}
}
else
{
uint8 x_225; 
x_225 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_225 == 0)
{
uint8 x_226; 
x_226 = !lean::is_exclusive(x_176);
if (x_226 == 0)
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; uint8 x_231; 
x_227 = lean::cnstr_get(x_176, 1);
x_228 = lean::cnstr_get(x_176, 2);
x_229 = lean::cnstr_get(x_176, 3);
x_230 = lean::cnstr_get(x_176, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_177);
if (x_231 == 0)
{
uint8 x_232; 
x_232 = 1;
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_232);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_232);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_177);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; uint8 x_237; obj* x_238; 
x_233 = lean::cnstr_get(x_177, 0);
x_234 = lean::cnstr_get(x_177, 1);
x_235 = lean::cnstr_get(x_177, 2);
x_236 = lean::cnstr_get(x_177, 3);
lean::inc(x_236);
lean::inc(x_235);
lean::inc(x_234);
lean::inc(x_233);
lean::dec(x_177);
x_237 = 1;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_234);
lean::cnstr_set(x_238, 2, x_235);
lean::cnstr_set(x_238, 3, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_237);
lean::cnstr_set(x_176, 3, x_31);
lean::cnstr_set(x_176, 2, x_30);
lean::cnstr_set(x_176, 1, x_29);
lean::cnstr_set(x_176, 0, x_229);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_237);
lean::cnstr_set(x_1, 3, x_176);
lean::cnstr_set(x_1, 2, x_228);
lean::cnstr_set(x_1, 1, x_227);
lean::cnstr_set(x_1, 0, x_238);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; obj* x_249; 
x_239 = lean::cnstr_get(x_176, 1);
x_240 = lean::cnstr_get(x_176, 2);
x_241 = lean::cnstr_get(x_176, 3);
lean::inc(x_241);
lean::inc(x_240);
lean::inc(x_239);
lean::dec(x_176);
x_242 = lean::cnstr_get(x_177, 0);
lean::inc(x_242);
x_243 = lean::cnstr_get(x_177, 1);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_177, 2);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_177, 3);
lean::inc(x_245);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_246 = x_177;
} else {
 lean::dec_ref(x_177);
 x_246 = lean::box(0);
}
x_247 = 1;
if (lean::is_scalar(x_246)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_246;
}
lean::cnstr_set(x_248, 0, x_242);
lean::cnstr_set(x_248, 1, x_243);
lean::cnstr_set(x_248, 2, x_244);
lean::cnstr_set(x_248, 3, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
x_249 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_249, 0, x_241);
lean::cnstr_set(x_249, 1, x_29);
lean::cnstr_set(x_249, 2, x_30);
lean::cnstr_set(x_249, 3, x_31);
lean::cnstr_set_scalar(x_249, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_249);
lean::cnstr_set(x_1, 2, x_240);
lean::cnstr_set(x_1, 1, x_239);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
obj* x_250; 
x_250 = lean::cnstr_get(x_176, 3);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
uint8 x_251; 
x_251 = !lean::is_exclusive(x_176);
if (x_251 == 0)
{
obj* x_252; obj* x_253; uint8 x_254; 
x_252 = lean::cnstr_get(x_176, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_176, 0);
lean::dec(x_253);
x_254 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_254);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
else
{
obj* x_255; obj* x_256; uint8 x_257; obj* x_258; 
x_255 = lean::cnstr_get(x_176, 1);
x_256 = lean::cnstr_get(x_176, 2);
lean::inc(x_256);
lean::inc(x_255);
lean::dec(x_176);
x_257 = 0;
x_258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_258, 0, x_177);
lean::cnstr_set(x_258, 1, x_255);
lean::cnstr_set(x_258, 2, x_256);
lean::cnstr_set(x_258, 3, x_250);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
uint8 x_259; 
x_259 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*4);
if (x_259 == 0)
{
uint8 x_260; 
lean::free_heap_obj(x_1);
x_260 = !lean::is_exclusive(x_176);
if (x_260 == 0)
{
obj* x_261; obj* x_262; obj* x_263; obj* x_264; uint8 x_265; 
x_261 = lean::cnstr_get(x_176, 1);
x_262 = lean::cnstr_get(x_176, 2);
x_263 = lean::cnstr_get(x_176, 3);
lean::dec(x_263);
x_264 = lean::cnstr_get(x_176, 0);
lean::dec(x_264);
x_265 = !lean::is_exclusive(x_250);
if (x_265 == 0)
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; uint8 x_270; 
x_266 = lean::cnstr_get(x_250, 0);
x_267 = lean::cnstr_get(x_250, 1);
x_268 = lean::cnstr_get(x_250, 2);
x_269 = lean::cnstr_get(x_250, 3);
lean::inc(x_177);
lean::cnstr_set(x_250, 3, x_266);
lean::cnstr_set(x_250, 2, x_262);
lean::cnstr_set(x_250, 1, x_261);
lean::cnstr_set(x_250, 0, x_177);
x_270 = !lean::is_exclusive(x_177);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_271 = lean::cnstr_get(x_177, 3);
lean::dec(x_271);
x_272 = lean::cnstr_get(x_177, 2);
lean::dec(x_272);
x_273 = lean::cnstr_get(x_177, 1);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_177, 0);
lean::dec(x_274);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
lean::cnstr_set(x_177, 3, x_31);
lean::cnstr_set(x_177, 2, x_30);
lean::cnstr_set(x_177, 1, x_29);
lean::cnstr_set(x_177, 0, x_269);
lean::cnstr_set(x_176, 3, x_177);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
else
{
obj* x_275; 
lean::dec(x_177);
lean::cnstr_set_scalar(x_250, sizeof(void*)*4, x_225);
x_275 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_275, 0, x_269);
lean::cnstr_set(x_275, 1, x_29);
lean::cnstr_set(x_275, 2, x_30);
lean::cnstr_set(x_275, 3, x_31);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_275);
lean::cnstr_set(x_176, 2, x_268);
lean::cnstr_set(x_176, 1, x_267);
lean::cnstr_set(x_176, 0, x_250);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_250, 0);
x_277 = lean::cnstr_get(x_250, 1);
x_278 = lean::cnstr_get(x_250, 2);
x_279 = lean::cnstr_get(x_250, 3);
lean::inc(x_279);
lean::inc(x_278);
lean::inc(x_277);
lean::inc(x_276);
lean::dec(x_250);
lean::inc(x_177);
x_280 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_280, 0, x_177);
lean::cnstr_set(x_280, 1, x_261);
lean::cnstr_set(x_280, 2, x_262);
lean::cnstr_set(x_280, 3, x_276);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_281 = x_177;
} else {
 lean::dec_ref(x_177);
 x_281 = lean::box(0);
}
lean::cnstr_set_scalar(x_280, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
lean::cnstr_set(x_282, 1, x_29);
lean::cnstr_set(x_282, 2, x_30);
lean::cnstr_set(x_282, 3, x_31);
lean::cnstr_set_scalar(x_282, sizeof(void*)*4, x_225);
lean::cnstr_set(x_176, 3, x_282);
lean::cnstr_set(x_176, 2, x_278);
lean::cnstr_set(x_176, 1, x_277);
lean::cnstr_set(x_176, 0, x_280);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_259);
return x_176;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_283 = lean::cnstr_get(x_176, 1);
x_284 = lean::cnstr_get(x_176, 2);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_176);
x_285 = lean::cnstr_get(x_250, 0);
lean::inc(x_285);
x_286 = lean::cnstr_get(x_250, 1);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_250, 2);
lean::inc(x_287);
x_288 = lean::cnstr_get(x_250, 3);
lean::inc(x_288);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 lean::cnstr_release(x_250, 3);
 x_289 = x_250;
} else {
 lean::dec_ref(x_250);
 x_289 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_177);
lean::cnstr_set(x_290, 1, x_283);
lean::cnstr_set(x_290, 2, x_284);
lean::cnstr_set(x_290, 3, x_285);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_291 = x_177;
} else {
 lean::dec_ref(x_177);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_225);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_288);
lean::cnstr_set(x_292, 1, x_29);
lean::cnstr_set(x_292, 2, x_30);
lean::cnstr_set(x_292, 3, x_31);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_225);
x_293 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_286);
lean::cnstr_set(x_293, 2, x_287);
lean::cnstr_set(x_293, 3, x_292);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_259);
return x_293;
}
}
else
{
uint8 x_294; 
x_294 = !lean::is_exclusive(x_176);
if (x_294 == 0)
{
obj* x_295; obj* x_296; uint8 x_297; 
x_295 = lean::cnstr_get(x_176, 3);
lean::dec(x_295);
x_296 = lean::cnstr_get(x_176, 0);
lean::dec(x_296);
x_297 = !lean::is_exclusive(x_177);
if (x_297 == 0)
{
uint8 x_298; 
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_259);
x_298 = 0;
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; uint8 x_304; 
x_299 = lean::cnstr_get(x_177, 0);
x_300 = lean::cnstr_get(x_177, 1);
x_301 = lean::cnstr_get(x_177, 2);
x_302 = lean::cnstr_get(x_177, 3);
lean::inc(x_302);
lean::inc(x_301);
lean::inc(x_300);
lean::inc(x_299);
lean::dec(x_177);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_300);
lean::cnstr_set(x_303, 2, x_301);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_259);
x_304 = 0;
lean::cnstr_set(x_176, 0, x_303);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_304);
lean::cnstr_set(x_1, 0, x_176);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; 
x_305 = lean::cnstr_get(x_176, 1);
x_306 = lean::cnstr_get(x_176, 2);
lean::inc(x_306);
lean::inc(x_305);
lean::dec(x_176);
x_307 = lean::cnstr_get(x_177, 0);
lean::inc(x_307);
x_308 = lean::cnstr_get(x_177, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_177, 2);
lean::inc(x_309);
x_310 = lean::cnstr_get(x_177, 3);
lean::inc(x_310);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_311 = x_177;
} else {
 lean::dec_ref(x_177);
 x_311 = lean::box(0);
}
if (lean::is_scalar(x_311)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_311;
}
lean::cnstr_set(x_312, 0, x_307);
lean::cnstr_set(x_312, 1, x_308);
lean::cnstr_set(x_312, 2, x_309);
lean::cnstr_set(x_312, 3, x_310);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_259);
x_313 = 0;
x_314 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_305);
lean::cnstr_set(x_314, 2, x_306);
lean::cnstr_set(x_314, 3, x_250);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
lean::cnstr_set(x_1, 0, x_314);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; uint8 x_319; 
x_315 = lean::cnstr_get(x_1, 0);
x_316 = lean::cnstr_get(x_1, 1);
x_317 = lean::cnstr_get(x_1, 2);
x_318 = lean::cnstr_get(x_1, 3);
lean::inc(x_318);
lean::inc(x_317);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_1);
x_319 = l_Lean_Name_quickLt(x_2, x_316);
if (x_319 == 0)
{
uint8 x_320; 
x_320 = l_Lean_Name_quickLt(x_316, x_2);
if (x_320 == 0)
{
obj* x_321; 
lean::dec(x_317);
lean::dec(x_316);
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_315);
lean::cnstr_set(x_321, 1, x_2);
lean::cnstr_set(x_321, 2, x_3);
lean::cnstr_set(x_321, 3, x_318);
lean::cnstr_set_scalar(x_321, sizeof(void*)*4, x_6);
return x_321;
}
else
{
uint8 x_322; 
x_322 = l_RBNode_isRed___main___rarg(x_318);
if (x_322 == 0)
{
obj* x_323; obj* x_324; 
x_323 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_318, x_2, x_3);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_315);
lean::cnstr_set(x_324, 1, x_316);
lean::cnstr_set(x_324, 2, x_317);
lean::cnstr_set(x_324, 3, x_323);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_6);
return x_324;
}
else
{
obj* x_325; 
x_325 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_318, x_2, x_3);
if (lean::obj_tag(x_325) == 0)
{
lean::dec(x_317);
lean::dec(x_316);
lean::dec(x_315);
return x_325;
}
else
{
obj* x_326; 
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_327; 
x_327 = lean::cnstr_get(x_325, 3);
lean::inc(x_327);
if (lean::obj_tag(x_327) == 0)
{
obj* x_328; obj* x_329; obj* x_330; uint8 x_331; obj* x_332; uint8 x_333; obj* x_334; 
x_328 = lean::cnstr_get(x_325, 1);
lean::inc(x_328);
x_329 = lean::cnstr_get(x_325, 2);
lean::inc(x_329);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_330 = x_325;
} else {
 lean::dec_ref(x_325);
 x_330 = lean::box(0);
}
x_331 = 0;
if (lean::is_scalar(x_330)) {
 x_332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_332 = x_330;
}
lean::cnstr_set(x_332, 0, x_327);
lean::cnstr_set(x_332, 1, x_328);
lean::cnstr_set(x_332, 2, x_329);
lean::cnstr_set(x_332, 3, x_327);
lean::cnstr_set_scalar(x_332, sizeof(void*)*4, x_331);
x_333 = 1;
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_315);
lean::cnstr_set(x_334, 1, x_316);
lean::cnstr_set(x_334, 2, x_317);
lean::cnstr_set(x_334, 3, x_332);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_333);
return x_334;
}
else
{
uint8 x_335; 
x_335 = lean::cnstr_get_scalar<uint8>(x_327, sizeof(void*)*4);
if (x_335 == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; obj* x_346; obj* x_347; 
x_336 = lean::cnstr_get(x_325, 1);
lean::inc(x_336);
x_337 = lean::cnstr_get(x_325, 2);
lean::inc(x_337);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_338 = x_325;
} else {
 lean::dec_ref(x_325);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_327, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
x_341 = lean::cnstr_get(x_327, 2);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_327, 3);
lean::inc(x_342);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_release(x_327, 1);
 lean::cnstr_release(x_327, 2);
 lean::cnstr_release(x_327, 3);
 x_343 = x_327;
} else {
 lean::dec_ref(x_327);
 x_343 = lean::box(0);
}
x_344 = 1;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_315);
lean::cnstr_set(x_345, 1, x_316);
lean::cnstr_set(x_345, 2, x_317);
lean::cnstr_set(x_345, 3, x_326);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_338)) {
 x_346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_346 = x_338;
}
lean::cnstr_set(x_346, 0, x_339);
lean::cnstr_set(x_346, 1, x_340);
lean::cnstr_set(x_346, 2, x_341);
lean::cnstr_set(x_346, 3, x_342);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_344);
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_336);
lean::cnstr_set(x_347, 2, x_337);
lean::cnstr_set(x_347, 3, x_346);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_335);
return x_347;
}
else
{
obj* x_348; obj* x_349; obj* x_350; uint8 x_351; obj* x_352; obj* x_353; 
x_348 = lean::cnstr_get(x_325, 1);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_325, 2);
lean::inc(x_349);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_350 = x_325;
} else {
 lean::dec_ref(x_325);
 x_350 = lean::box(0);
}
x_351 = 0;
if (lean::is_scalar(x_350)) {
 x_352 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_352 = x_350;
}
lean::cnstr_set(x_352, 0, x_326);
lean::cnstr_set(x_352, 1, x_348);
lean::cnstr_set(x_352, 2, x_349);
lean::cnstr_set(x_352, 3, x_327);
lean::cnstr_set_scalar(x_352, sizeof(void*)*4, x_351);
x_353 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_353, 0, x_315);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_317);
lean::cnstr_set(x_353, 3, x_352);
lean::cnstr_set_scalar(x_353, sizeof(void*)*4, x_335);
return x_353;
}
}
}
else
{
uint8 x_354; 
x_354 = lean::cnstr_get_scalar<uint8>(x_326, sizeof(void*)*4);
if (x_354 == 0)
{
obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; 
x_355 = lean::cnstr_get(x_325, 1);
lean::inc(x_355);
x_356 = lean::cnstr_get(x_325, 2);
lean::inc(x_356);
x_357 = lean::cnstr_get(x_325, 3);
lean::inc(x_357);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_358 = x_325;
} else {
 lean::dec_ref(x_325);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_326, 0);
lean::inc(x_359);
x_360 = lean::cnstr_get(x_326, 1);
lean::inc(x_360);
x_361 = lean::cnstr_get(x_326, 2);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_326, 3);
lean::inc(x_362);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_363 = x_326;
} else {
 lean::dec_ref(x_326);
 x_363 = lean::box(0);
}
x_364 = 1;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_315);
lean::cnstr_set(x_365, 1, x_316);
lean::cnstr_set(x_365, 2, x_317);
lean::cnstr_set(x_365, 3, x_359);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
if (lean::is_scalar(x_358)) {
 x_366 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_366 = x_358;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set(x_366, 1, x_355);
lean::cnstr_set(x_366, 2, x_356);
lean::cnstr_set(x_366, 3, x_357);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_364);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_365);
lean::cnstr_set(x_367, 1, x_360);
lean::cnstr_set(x_367, 2, x_361);
lean::cnstr_set(x_367, 3, x_366);
lean::cnstr_set_scalar(x_367, sizeof(void*)*4, x_354);
return x_367;
}
else
{
obj* x_368; 
x_368 = lean::cnstr_get(x_325, 3);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_369; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_374; 
x_369 = lean::cnstr_get(x_325, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_325, 2);
lean::inc(x_370);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_371 = x_325;
} else {
 lean::dec_ref(x_325);
 x_371 = lean::box(0);
}
x_372 = 0;
if (lean::is_scalar(x_371)) {
 x_373 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_373 = x_371;
}
lean::cnstr_set(x_373, 0, x_326);
lean::cnstr_set(x_373, 1, x_369);
lean::cnstr_set(x_373, 2, x_370);
lean::cnstr_set(x_373, 3, x_368);
lean::cnstr_set_scalar(x_373, sizeof(void*)*4, x_372);
x_374 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_374, 0, x_315);
lean::cnstr_set(x_374, 1, x_316);
lean::cnstr_set(x_374, 2, x_317);
lean::cnstr_set(x_374, 3, x_373);
lean::cnstr_set_scalar(x_374, sizeof(void*)*4, x_354);
return x_374;
}
else
{
uint8 x_375; 
x_375 = lean::cnstr_get_scalar<uint8>(x_368, sizeof(void*)*4);
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_376 = lean::cnstr_get(x_325, 1);
lean::inc(x_376);
x_377 = lean::cnstr_get(x_325, 2);
lean::inc(x_377);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_378 = x_325;
} else {
 lean::dec_ref(x_325);
 x_378 = lean::box(0);
}
x_379 = lean::cnstr_get(x_368, 0);
lean::inc(x_379);
x_380 = lean::cnstr_get(x_368, 1);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_368, 2);
lean::inc(x_381);
x_382 = lean::cnstr_get(x_368, 3);
lean::inc(x_382);
if (lean::is_exclusive(x_368)) {
 lean::cnstr_release(x_368, 0);
 lean::cnstr_release(x_368, 1);
 lean::cnstr_release(x_368, 2);
 lean::cnstr_release(x_368, 3);
 x_383 = x_368;
} else {
 lean::dec_ref(x_368);
 x_383 = lean::box(0);
}
lean::inc(x_326);
if (lean::is_scalar(x_383)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_383;
}
lean::cnstr_set(x_384, 0, x_315);
lean::cnstr_set(x_384, 1, x_316);
lean::cnstr_set(x_384, 2, x_317);
lean::cnstr_set(x_384, 3, x_326);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_385 = x_326;
} else {
 lean::dec_ref(x_326);
 x_385 = lean::box(0);
}
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_385)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_385;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_380);
lean::cnstr_set(x_386, 2, x_381);
lean::cnstr_set(x_386, 3, x_382);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_354);
if (lean::is_scalar(x_378)) {
 x_387 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_387 = x_378;
}
lean::cnstr_set(x_387, 0, x_384);
lean::cnstr_set(x_387, 1, x_376);
lean::cnstr_set(x_387, 2, x_377);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_375);
return x_387;
}
else
{
obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; uint8 x_397; obj* x_398; obj* x_399; 
x_388 = lean::cnstr_get(x_325, 1);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_325, 2);
lean::inc(x_389);
if (lean::is_exclusive(x_325)) {
 lean::cnstr_release(x_325, 0);
 lean::cnstr_release(x_325, 1);
 lean::cnstr_release(x_325, 2);
 lean::cnstr_release(x_325, 3);
 x_390 = x_325;
} else {
 lean::dec_ref(x_325);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_326, 0);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_326, 1);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_326, 2);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_326, 3);
lean::inc(x_394);
if (lean::is_exclusive(x_326)) {
 lean::cnstr_release(x_326, 0);
 lean::cnstr_release(x_326, 1);
 lean::cnstr_release(x_326, 2);
 lean::cnstr_release(x_326, 3);
 x_395 = x_326;
} else {
 lean::dec_ref(x_326);
 x_395 = lean::box(0);
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_391);
lean::cnstr_set(x_396, 1, x_392);
lean::cnstr_set(x_396, 2, x_393);
lean::cnstr_set(x_396, 3, x_394);
lean::cnstr_set_scalar(x_396, sizeof(void*)*4, x_375);
x_397 = 0;
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_396);
lean::cnstr_set(x_398, 1, x_388);
lean::cnstr_set(x_398, 2, x_389);
lean::cnstr_set(x_398, 3, x_368);
lean::cnstr_set_scalar(x_398, sizeof(void*)*4, x_397);
x_399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_399, 0, x_315);
lean::cnstr_set(x_399, 1, x_316);
lean::cnstr_set(x_399, 2, x_317);
lean::cnstr_set(x_399, 3, x_398);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_375);
return x_399;
}
}
}
}
}
}
}
}
else
{
uint8 x_400; 
x_400 = l_RBNode_isRed___main___rarg(x_315);
if (x_400 == 0)
{
obj* x_401; obj* x_402; 
x_401 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_315, x_2, x_3);
x_402 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_316);
lean::cnstr_set(x_402, 2, x_317);
lean::cnstr_set(x_402, 3, x_318);
lean::cnstr_set_scalar(x_402, sizeof(void*)*4, x_6);
return x_402;
}
else
{
obj* x_403; 
x_403 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_315, x_2, x_3);
if (lean::obj_tag(x_403) == 0)
{
lean::dec(x_318);
lean::dec(x_317);
lean::dec(x_316);
return x_403;
}
else
{
obj* x_404; 
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
if (lean::obj_tag(x_404) == 0)
{
obj* x_405; 
x_405 = lean::cnstr_get(x_403, 3);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_406; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; uint8 x_411; obj* x_412; 
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_403, 2);
lean::inc(x_407);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_408 = x_403;
} else {
 lean::dec_ref(x_403);
 x_408 = lean::box(0);
}
x_409 = 0;
if (lean::is_scalar(x_408)) {
 x_410 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_410 = x_408;
}
lean::cnstr_set(x_410, 0, x_405);
lean::cnstr_set(x_410, 1, x_406);
lean::cnstr_set(x_410, 2, x_407);
lean::cnstr_set(x_410, 3, x_405);
lean::cnstr_set_scalar(x_410, sizeof(void*)*4, x_409);
x_411 = 1;
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_316);
lean::cnstr_set(x_412, 2, x_317);
lean::cnstr_set(x_412, 3, x_318);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
uint8 x_413; 
x_413 = lean::cnstr_get_scalar<uint8>(x_405, sizeof(void*)*4);
if (x_413 == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; 
x_414 = lean::cnstr_get(x_403, 1);
lean::inc(x_414);
x_415 = lean::cnstr_get(x_403, 2);
lean::inc(x_415);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_416 = x_403;
} else {
 lean::dec_ref(x_403);
 x_416 = lean::box(0);
}
x_417 = lean::cnstr_get(x_405, 0);
lean::inc(x_417);
x_418 = lean::cnstr_get(x_405, 1);
lean::inc(x_418);
x_419 = lean::cnstr_get(x_405, 2);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_405, 3);
lean::inc(x_420);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 lean::cnstr_release(x_405, 2);
 lean::cnstr_release(x_405, 3);
 x_421 = x_405;
} else {
 lean::dec_ref(x_405);
 x_421 = lean::box(0);
}
x_422 = 1;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_404);
lean::cnstr_set(x_423, 1, x_414);
lean::cnstr_set(x_423, 2, x_415);
lean::cnstr_set(x_423, 3, x_417);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
if (lean::is_scalar(x_416)) {
 x_424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_424 = x_416;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set(x_424, 1, x_316);
lean::cnstr_set(x_424, 2, x_317);
lean::cnstr_set(x_424, 3, x_318);
lean::cnstr_set_scalar(x_424, sizeof(void*)*4, x_422);
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_418);
lean::cnstr_set(x_425, 2, x_419);
lean::cnstr_set(x_425, 3, x_424);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_413);
return x_425;
}
else
{
obj* x_426; obj* x_427; obj* x_428; uint8 x_429; obj* x_430; obj* x_431; 
x_426 = lean::cnstr_get(x_403, 1);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_403, 2);
lean::inc(x_427);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_428 = x_403;
} else {
 lean::dec_ref(x_403);
 x_428 = lean::box(0);
}
x_429 = 0;
if (lean::is_scalar(x_428)) {
 x_430 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_430 = x_428;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_426);
lean::cnstr_set(x_430, 2, x_427);
lean::cnstr_set(x_430, 3, x_405);
lean::cnstr_set_scalar(x_430, sizeof(void*)*4, x_429);
x_431 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_316);
lean::cnstr_set(x_431, 2, x_317);
lean::cnstr_set(x_431, 3, x_318);
lean::cnstr_set_scalar(x_431, sizeof(void*)*4, x_413);
return x_431;
}
}
}
else
{
uint8 x_432; 
x_432 = lean::cnstr_get_scalar<uint8>(x_404, sizeof(void*)*4);
if (x_432 == 0)
{
obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; obj* x_445; 
x_433 = lean::cnstr_get(x_403, 1);
lean::inc(x_433);
x_434 = lean::cnstr_get(x_403, 2);
lean::inc(x_434);
x_435 = lean::cnstr_get(x_403, 3);
lean::inc(x_435);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_436 = x_403;
} else {
 lean::dec_ref(x_403);
 x_436 = lean::box(0);
}
x_437 = lean::cnstr_get(x_404, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_404, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_404, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_404, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_441 = x_404;
} else {
 lean::dec_ref(x_404);
 x_441 = lean::box(0);
}
x_442 = 1;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_437);
lean::cnstr_set(x_443, 1, x_438);
lean::cnstr_set(x_443, 2, x_439);
lean::cnstr_set(x_443, 3, x_440);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
if (lean::is_scalar(x_436)) {
 x_444 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_444 = x_436;
}
lean::cnstr_set(x_444, 0, x_435);
lean::cnstr_set(x_444, 1, x_316);
lean::cnstr_set(x_444, 2, x_317);
lean::cnstr_set(x_444, 3, x_318);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_442);
x_445 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_445, 0, x_443);
lean::cnstr_set(x_445, 1, x_433);
lean::cnstr_set(x_445, 2, x_434);
lean::cnstr_set(x_445, 3, x_444);
lean::cnstr_set_scalar(x_445, sizeof(void*)*4, x_432);
return x_445;
}
else
{
obj* x_446; 
x_446 = lean::cnstr_get(x_403, 3);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_447; obj* x_448; obj* x_449; uint8 x_450; obj* x_451; obj* x_452; 
x_447 = lean::cnstr_get(x_403, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_403, 2);
lean::inc(x_448);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_449 = x_403;
} else {
 lean::dec_ref(x_403);
 x_449 = lean::box(0);
}
x_450 = 0;
if (lean::is_scalar(x_449)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_449;
}
lean::cnstr_set(x_451, 0, x_404);
lean::cnstr_set(x_451, 1, x_447);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_446);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_450);
x_452 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_316);
lean::cnstr_set(x_452, 2, x_317);
lean::cnstr_set(x_452, 3, x_318);
lean::cnstr_set_scalar(x_452, sizeof(void*)*4, x_432);
return x_452;
}
else
{
uint8 x_453; 
x_453 = lean::cnstr_get_scalar<uint8>(x_446, sizeof(void*)*4);
if (x_453 == 0)
{
obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; 
x_454 = lean::cnstr_get(x_403, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_403, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_456 = x_403;
} else {
 lean::dec_ref(x_403);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_446, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_446, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_446, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_446, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 lean::cnstr_release(x_446, 1);
 lean::cnstr_release(x_446, 2);
 lean::cnstr_release(x_446, 3);
 x_461 = x_446;
} else {
 lean::dec_ref(x_446);
 x_461 = lean::box(0);
}
lean::inc(x_404);
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_404);
lean::cnstr_set(x_462, 1, x_454);
lean::cnstr_set(x_462, 2, x_455);
lean::cnstr_set(x_462, 3, x_457);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_463 = x_404;
} else {
 lean::dec_ref(x_404);
 x_463 = lean::box(0);
}
lean::cnstr_set_scalar(x_462, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_463)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_463;
}
lean::cnstr_set(x_464, 0, x_460);
lean::cnstr_set(x_464, 1, x_316);
lean::cnstr_set(x_464, 2, x_317);
lean::cnstr_set(x_464, 3, x_318);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_432);
if (lean::is_scalar(x_456)) {
 x_465 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_465 = x_456;
}
lean::cnstr_set(x_465, 0, x_462);
lean::cnstr_set(x_465, 1, x_458);
lean::cnstr_set(x_465, 2, x_459);
lean::cnstr_set(x_465, 3, x_464);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_453);
return x_465;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; uint8 x_475; obj* x_476; obj* x_477; 
x_466 = lean::cnstr_get(x_403, 1);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_403, 2);
lean::inc(x_467);
if (lean::is_exclusive(x_403)) {
 lean::cnstr_release(x_403, 0);
 lean::cnstr_release(x_403, 1);
 lean::cnstr_release(x_403, 2);
 lean::cnstr_release(x_403, 3);
 x_468 = x_403;
} else {
 lean::dec_ref(x_403);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_404, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get(x_404, 1);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_404, 2);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_404, 3);
lean::inc(x_472);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 lean::cnstr_release(x_404, 2);
 lean::cnstr_release(x_404, 3);
 x_473 = x_404;
} else {
 lean::dec_ref(x_404);
 x_473 = lean::box(0);
}
if (lean::is_scalar(x_473)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_473;
}
lean::cnstr_set(x_474, 0, x_469);
lean::cnstr_set(x_474, 1, x_470);
lean::cnstr_set(x_474, 2, x_471);
lean::cnstr_set(x_474, 3, x_472);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_453);
x_475 = 0;
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_474);
lean::cnstr_set(x_476, 1, x_466);
lean::cnstr_set(x_476, 2, x_467);
lean::cnstr_set(x_476, 3, x_446);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_475);
x_477 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_316);
lean::cnstr_set(x_477, 2, x_317);
lean::cnstr_set(x_477, 3, x_318);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_453);
return x_477;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_addBuiltinCommandElab___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_addBuiltinCommandElab___spec__7(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_AssocList_mfoldl___main___at_Lean_addBuiltinCommandElab___spec__11(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_moveEntries___main___at_Lean_addBuiltinCommandElab___spec__10(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_mfoldl___main___at_Lean_addBuiltinCommandElab___spec__11(x_3, x_6);
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
obj* l_HashMapImp_expand___at_Lean_addBuiltinCommandElab___spec__9(obj* x_1, obj* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_addBuiltinCommandElab___spec__10(x_8, x_2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(obj* x_1, obj* x_2, obj* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(x_1, x_2, x_12);
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
obj* l_HashMapImp_insert___at_Lean_addBuiltinCommandElab___spec__8(obj* x_1, obj* x_2, obj* x_3) {
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
x_13 = l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(x_2, x_12);
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
x_20 = l_HashMapImp_expand___at_Lean_addBuiltinCommandElab___spec__9(x_15, x_18);
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
x_21 = l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(x_2, x_3, x_12);
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
x_32 = l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(x_2, x_31);
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
x_39 = l_HashMapImp_expand___at_Lean_addBuiltinCommandElab___spec__9(x_34, x_37);
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
x_41 = l_AssocList_replace___main___at_Lean_addBuiltinCommandElab___spec__12(x_2, x_3, x_31);
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
obj* l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = l_RBNode_insert___at_Lean_addBuiltinCommandElab___spec__6(x_6, x_2, x_3);
lean::cnstr_set(x_1, 1, x_7);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_RBNode_insert___at_Lean_addBuiltinCommandElab___spec__6(x_9, x_2, x_3);
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_addBuiltinCommandElab___spec__8(x_13, x_2, x_3);
lean::cnstr_set(x_1, 0, x_14);
return x_1;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_addBuiltinCommandElab___spec__8(x_15, x_2, x_3);
x_18 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
obj* _init_l_Lean_addBuiltinCommandElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid builtin command elaborator, elaborator for '");
return x_1;
}
}
obj* l_Lean_addBuiltinCommandElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_builtinCommandElabTable;
x_6 = lean::io_ref_get(x_5, x_4);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1(x_8, x_1);
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
x_17 = l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(x_13, x_1, x_3);
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
x_21 = l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(x_13, x_1, x_3);
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
x_34 = l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(x_27, x_1, x_3);
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
x_46 = l_Lean_addBuiltinCommandElab___closed__1;
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
x_52 = l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1(x_50, x_1);
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
x_64 = l_Lean_SMap_insert___main___at_Lean_addBuiltinCommandElab___spec__5(x_56, x_1, x_3);
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
x_76 = l_Lean_addBuiltinCommandElab___closed__1;
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
obj* l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_addBuiltinCommandElab___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_addBuiltinCommandElab___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_SMap_contains___main___at_Lean_addBuiltinCommandElab___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_addBuiltinCommandElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_addBuiltinCommandElab(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_checkSyntaxNodeKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed");
return x_1;
}
}
obj* l_Lean_checkSyntaxNodeKind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_isValidSyntaxNodeKind(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Lean_checkSyntaxNodeKind___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = l_Lean_checkSyntaxNodeKind___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
lean::cnstr_set(x_3, 0, x_1);
return x_3;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8 x_16; 
lean::dec(x_1);
x_16 = !lean::is_exclusive(x_3);
if (x_16 == 0)
{
return x_3;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_3, 0);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_3);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
}
}
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = l_Lean_checkSyntaxNodeKind___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = l_Lean_checkSyntaxNodeKind___closed__1;
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_12 = l_Lean_Name_append___main(x_10, x_1);
x_13 = l_Lean_checkSyntaxNodeKind(x_12, x_3);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_1);
return x_13;
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::dec(x_15);
x_16 = lean::box(0);
lean::cnstr_set_tag(x_13, 0);
lean::cnstr_set(x_13, 0, x_16);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_2 = x_11;
x_3 = x_20;
goto _start;
}
}
}
}
}
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_checkSyntaxNodeKindAtNamespaces(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_checkSyntaxNodeKindAtNamespaces___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_checkSyntaxNodeKindAtNamespaces___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_checkSyntaxNodeKindAtNamespaces(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_syntaxNodeKindOfAttrParam___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("syntax node kind is missing");
return x_1;
}
}
obj* _init_l_Lean_syntaxNodeKindOfAttrParam___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid syntax node kind '");
return x_1;
}
}
obj* l_Lean_syntaxNodeKindOfAttrParam(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
x_8 = l_Lean_syntaxNodeKindOfAttrParam___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_10 = l_Lean_syntaxNodeKindOfAttrParam___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_13 = lean::get_namespaces_core(x_1);
lean::inc(x_12);
x_14 = l_Lean_Name_append___main(x_2, x_12);
x_15 = l_System_FilePath_dirName___closed__1;
lean::inc(x_12);
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_12);
x_17 = l_Lean_syntaxNodeKindOfAttrParam___closed__2;
x_18 = lean::string_append(x_17, x_16);
lean::dec(x_16);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean::string_append(x_18, x_19);
lean::inc(x_12);
x_21 = l_Lean_checkSyntaxNodeKind(x_12, x_4);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_20);
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_12);
return x_21;
}
else
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::dec(x_23);
x_24 = lean::box(0);
lean::cnstr_set_tag(x_21, 0);
lean::cnstr_set(x_21, 0, x_24);
x_25 = l_Lean_checkSyntaxNodeKindAtNamespaces___main(x_12, x_13, x_21);
lean::dec(x_13);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_20);
lean::dec(x_14);
return x_25;
}
else
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set_tag(x_25, 0);
lean::cnstr_set(x_25, 0, x_24);
x_28 = l_Lean_checkSyntaxNodeKind(x_14, x_25);
if (lean::obj_tag(x_28) == 0)
{
lean::dec(x_20);
return x_28;
}
else
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; 
x_30 = lean::cnstr_get(x_28, 0);
lean::dec(x_30);
lean::cnstr_set(x_28, 0, x_20);
return x_28;
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_20);
lean::cnstr_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_25, 1);
lean::inc(x_33);
lean::dec(x_25);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_checkSyntaxNodeKind(x_14, x_34);
if (lean::obj_tag(x_35) == 0)
{
lean::dec(x_20);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 lean::cnstr_release(x_35, 1);
 x_37 = x_35;
} else {
 lean::dec_ref(x_35);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_20);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_21, 1);
lean::inc(x_39);
lean::dec(x_21);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = l_Lean_checkSyntaxNodeKindAtNamespaces___main(x_12, x_13, x_41);
lean::dec(x_13);
if (lean::obj_tag(x_42) == 0)
{
lean::dec(x_20);
lean::dec(x_14);
return x_42;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_44 = x_42;
} else {
 lean::dec_ref(x_42);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_44;
 lean::cnstr_set_tag(x_45, 0);
}
lean::cnstr_set(x_45, 0, x_40);
lean::cnstr_set(x_45, 1, x_43);
x_46 = l_Lean_checkSyntaxNodeKind(x_14, x_45);
if (lean::obj_tag(x_46) == 0)
{
lean::dec(x_20);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_20);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
}
}
obj* l_Lean_syntaxNodeKindOfAttrParam___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_declareBuiltinElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_regBuiltinTermElab");
return x_1;
}
}
obj* _init_l_Lean_declareBuiltinElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_declareBuiltinElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_declareBuiltinElab___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to emit registration code for builtin term elaborator '");
return x_1;
}
}
obj* l_Lean_declareBuiltinElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_6 = l_Lean_declareBuiltinElab___closed__2;
lean::inc(x_4);
x_7 = l_Lean_Name_append___main(x_6, x_4);
x_8 = lean::box(0);
x_9 = l_Lean_nameToExprAux___main(x_3);
lean::inc(x_4);
x_10 = l_Lean_nameToExprAux___main(x_4);
lean::inc(x_4);
x_11 = lean_expr_mk_const(x_4, x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_Lean_mkCApp(x_2, x_14);
x_16 = l_Lean_Parser_declareBuiltinParser___closed__5;
lean::inc(x_7);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_8);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::box(0);
x_19 = 0;
x_20 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_15);
lean::cnstr_set(x_20, 2, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*3, x_19);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = l_Lean_Options_empty;
x_23 = lean_add_and_compile(x_1, x_22, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
lean::dec(x_7);
x_24 = !lean::is_exclusive(x_5);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_5, 0);
lean::dec(x_25);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_4);
x_28 = l_Lean_declareBuiltinElab___closed__3;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean::string_append(x_29, x_30);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_31);
return x_5;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_5, 1);
lean::inc(x_32);
lean::dec(x_5);
x_33 = l_System_FilePath_dirName___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_4);
x_35 = l_Lean_declareBuiltinElab___closed__3;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean::string_append(x_36, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_32);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_4);
x_40 = lean::cnstr_get(x_23, 0);
lean::inc(x_40);
lean::dec(x_23);
x_41 = l_Lean_initAttr;
x_42 = lean::box(0);
x_43 = l_Lean_ParametricAttribute_setParam___rarg(x_41, x_40, x_7, x_42);
x_44 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_43, x_5);
lean::dec(x_43);
return x_44;
}
}
}
obj* l_Lean_declareBuiltinElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_declareBuiltinElab(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_declareBuiltinTermElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("addBuiltinTermElab");
return x_1;
}
}
obj* _init_l_Lean_declareBuiltinTermElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_declareBuiltinTermElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_declareBuiltinTermElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_declareBuiltinTermElab___closed__2;
x_6 = l_Lean_declareBuiltinElab(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_declareBuiltinTermElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_declareBuiltinTermElab(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_declareBuiltinCommandElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("addBuiltinCommandElab");
return x_1;
}
}
obj* _init_l_Lean_declareBuiltinCommandElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_declareBuiltinCommandElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_declareBuiltinCommandElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_declareBuiltinCommandElab___closed__2;
x_6 = l_Lean_declareBuiltinElab(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_declareBuiltinCommandElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_declareBuiltinCommandElab(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid attribute 'builtinTermElab', must be persistent");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected term elaborator type at '");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' `TermElab` expected");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("TermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
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
x_8 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
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
x_10 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
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
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::cnstr_set(x_16, 0, x_14);
lean::inc(x_2);
lean::inc(x_1);
x_20 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_1);
x_21 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_24 = l_Lean_ConstantInfo_type(x_23);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 4)
{
obj* x_25; obj* x_26; uint8 x_27; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_27 = lean_name_dec_eq(x_25, x_26);
lean::dec(x_25);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_1);
x_28 = l_System_FilePath_dirName___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_2);
x_30 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_32 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_33 = lean::string_append(x_31, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_19);
return x_34;
}
else
{
obj* x_35; 
lean::dec(x_19);
x_35 = l_Lean_declareBuiltinTermElab(x_1, x_18, x_2, x_16);
lean::dec(x_1);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_1);
x_36 = l_System_FilePath_dirName___closed__1;
x_37 = l_Lean_Name_toStringWithSep___main(x_36, x_2);
x_38 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_39 = lean::string_append(x_38, x_37);
lean::dec(x_37);
x_40 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_41 = lean::string_append(x_39, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_19);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_16, 0);
x_44 = lean::cnstr_get(x_16, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_16);
lean::inc(x_44);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_14);
lean::cnstr_set(x_45, 1, x_44);
lean::inc(x_2);
lean::inc(x_1);
x_46 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_2);
lean::dec(x_1);
x_47 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
return x_48;
}
else
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_50 = l_Lean_ConstantInfo_type(x_49);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 4)
{
obj* x_51; obj* x_52; uint8 x_53; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_52 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_53 = lean_name_dec_eq(x_51, x_52);
lean::dec(x_51);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_1);
x_54 = l_System_FilePath_dirName___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_2);
x_56 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_58 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_59 = lean::string_append(x_57, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_44);
return x_60;
}
else
{
obj* x_61; 
lean::dec(x_44);
x_61 = l_Lean_declareBuiltinTermElab(x_1, x_43, x_2, x_45);
lean::dec(x_1);
return x_61;
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_50);
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_1);
x_62 = l_System_FilePath_dirName___closed__1;
x_63 = l_Lean_Name_toStringWithSep___main(x_62, x_2);
x_64 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_65 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_66 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_67 = lean::string_append(x_65, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_44);
return x_68;
}
}
}
}
else
{
uint8 x_69; 
lean::dec(x_2);
lean::dec(x_1);
x_69 = !lean::is_exclusive(x_16);
if (x_69 == 0)
{
return x_16;
}
else
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_16, 0);
x_71 = lean::cnstr_get(x_16, 1);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_16);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_5, 1);
lean::inc(x_73);
lean::dec(x_5);
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
x_76 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean::inc(x_1);
x_77 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_76, x_3, x_75);
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
lean::inc(x_79);
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_74);
lean::cnstr_set(x_81, 1, x_79);
lean::inc(x_2);
lean::inc(x_1);
x_82 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_84; 
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_2);
lean::dec(x_1);
x_83 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_79);
return x_84;
}
else
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
lean::dec(x_82);
x_86 = l_Lean_ConstantInfo_type(x_85);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 4)
{
obj* x_87; obj* x_88; uint8 x_89; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_88 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_89 = lean_name_dec_eq(x_87, x_88);
lean::dec(x_87);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_1);
x_90 = l_System_FilePath_dirName___closed__1;
x_91 = l_Lean_Name_toStringWithSep___main(x_90, x_2);
x_92 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_93 = lean::string_append(x_92, x_91);
lean::dec(x_91);
x_94 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_95 = lean::string_append(x_93, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_79);
return x_96;
}
else
{
obj* x_97; 
lean::dec(x_79);
x_97 = l_Lean_declareBuiltinTermElab(x_1, x_78, x_2, x_81);
lean::dec(x_1);
return x_97;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_86);
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_1);
x_98 = l_System_FilePath_dirName___closed__1;
x_99 = l_Lean_Name_toStringWithSep___main(x_98, x_2);
x_100 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_101 = lean::string_append(x_100, x_99);
lean::dec(x_99);
x_102 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_103 = lean::string_append(x_101, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_79);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_2);
lean::dec(x_1);
x_105 = lean::cnstr_get(x_77, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_77, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_107 = x_77;
} else {
 lean::dec_ref(x_77);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinTermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Builtin term elaborator");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinTermElabAttr___closed__6;
x_4 = l_Lean_registerBuiltinTermElabAttr___closed__3;
x_5 = l_Lean_registerBuiltinTermElabAttr___closed__4;
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
obj* l_Lean_registerBuiltinTermElabAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_registerBuiltinTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid attribute 'builtinCommandElab', must be persistent");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected command elaborator type at '");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' `CommandElab` expected");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("CommandElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
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
x_8 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1;
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
x_10 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1;
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
x_15 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
lean::inc(x_1);
x_16 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_15, x_3, x_5);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::cnstr_set(x_16, 0, x_14);
lean::inc(x_2);
lean::inc(x_1);
x_20 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_1);
x_21 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_24 = l_Lean_ConstantInfo_type(x_23);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 4)
{
obj* x_25; obj* x_26; uint8 x_27; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5;
x_27 = lean_name_dec_eq(x_25, x_26);
lean::dec(x_25);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_1);
x_28 = l_System_FilePath_dirName___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_2);
x_30 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_32 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_33 = lean::string_append(x_31, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_19);
return x_34;
}
else
{
obj* x_35; 
lean::dec(x_19);
x_35 = l_Lean_declareBuiltinCommandElab(x_1, x_18, x_2, x_16);
lean::dec(x_1);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_1);
x_36 = l_System_FilePath_dirName___closed__1;
x_37 = l_Lean_Name_toStringWithSep___main(x_36, x_2);
x_38 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_39 = lean::string_append(x_38, x_37);
lean::dec(x_37);
x_40 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_41 = lean::string_append(x_39, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_19);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::cnstr_get(x_16, 0);
x_44 = lean::cnstr_get(x_16, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_16);
lean::inc(x_44);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_14);
lean::cnstr_set(x_45, 1, x_44);
lean::inc(x_2);
lean::inc(x_1);
x_46 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_2);
lean::dec(x_1);
x_47 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
return x_48;
}
else
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_50 = l_Lean_ConstantInfo_type(x_49);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 4)
{
obj* x_51; obj* x_52; uint8 x_53; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
lean::dec(x_50);
x_52 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5;
x_53 = lean_name_dec_eq(x_51, x_52);
lean::dec(x_51);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_1);
x_54 = l_System_FilePath_dirName___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_2);
x_56 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_58 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_59 = lean::string_append(x_57, x_58);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_44);
return x_60;
}
else
{
obj* x_61; 
lean::dec(x_44);
x_61 = l_Lean_declareBuiltinCommandElab(x_1, x_43, x_2, x_45);
lean::dec(x_1);
return x_61;
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_50);
lean::dec(x_45);
lean::dec(x_43);
lean::dec(x_1);
x_62 = l_System_FilePath_dirName___closed__1;
x_63 = l_Lean_Name_toStringWithSep___main(x_62, x_2);
x_64 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_65 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_66 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_67 = lean::string_append(x_65, x_66);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_44);
return x_68;
}
}
}
}
else
{
uint8 x_69; 
lean::dec(x_2);
lean::dec(x_1);
x_69 = !lean::is_exclusive(x_16);
if (x_69 == 0)
{
return x_16;
}
else
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_16, 0);
x_71 = lean::cnstr_get(x_16, 1);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_16);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_5, 1);
lean::inc(x_73);
lean::dec(x_5);
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
x_76 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
lean::inc(x_1);
x_77 = l_Lean_syntaxNodeKindOfAttrParam(x_1, x_76, x_3, x_75);
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
lean::inc(x_79);
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_74);
lean::cnstr_set(x_81, 1, x_79);
lean::inc(x_2);
lean::inc(x_1);
x_82 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_84; 
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_2);
lean::dec(x_1);
x_83 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_79);
return x_84;
}
else
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
lean::dec(x_82);
x_86 = l_Lean_ConstantInfo_type(x_85);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 4)
{
obj* x_87; obj* x_88; uint8 x_89; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
lean::dec(x_86);
x_88 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5;
x_89 = lean_name_dec_eq(x_87, x_88);
lean::dec(x_87);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_1);
x_90 = l_System_FilePath_dirName___closed__1;
x_91 = l_Lean_Name_toStringWithSep___main(x_90, x_2);
x_92 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_93 = lean::string_append(x_92, x_91);
lean::dec(x_91);
x_94 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_95 = lean::string_append(x_93, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_79);
return x_96;
}
else
{
obj* x_97; 
lean::dec(x_79);
x_97 = l_Lean_declareBuiltinCommandElab(x_1, x_78, x_2, x_81);
lean::dec(x_1);
return x_97;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_86);
lean::dec(x_81);
lean::dec(x_78);
lean::dec(x_1);
x_98 = l_System_FilePath_dirName___closed__1;
x_99 = l_Lean_Name_toStringWithSep___main(x_98, x_2);
x_100 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_101 = lean::string_append(x_100, x_99);
lean::dec(x_99);
x_102 = l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_103 = lean::string_append(x_101, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_79);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_2);
lean::dec(x_1);
x_105 = lean::cnstr_get(x_77, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_77, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_107 = x_77;
} else {
 lean::dec_ref(x_77);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinCommandElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerBuiltinCommandElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinCommandElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinCommandElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Builtin command elaborator");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerBuiltinCommandElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinCommandElabAttr___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_1 = l_Lean_registerBuiltinCommandElabAttr___closed__2;
x_2 = l_Lean_registerBuiltinCommandElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinCommandElabAttr___closed__6;
x_4 = l_Lean_registerBuiltinCommandElabAttr___closed__3;
x_5 = l_Lean_registerBuiltinCommandElabAttr___closed__4;
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
obj* l_Lean_registerBuiltinCommandElabAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_registerBuiltinCommandElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
obj* l_Lean_registerBuiltinCommandElabAttr___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_registerBuiltinCommandElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_ElabAttribute_Inhabited___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::box(0);
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_10 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_11 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_12 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
lean::cnstr_set(x_12, 2, x_8);
lean::cnstr_set(x_12, 3, x_9);
lean::cnstr_set(x_12, 4, x_10);
lean::cnstr_set(x_12, 5, x_11);
x_13 = l_Lean_AttributeImpl_inhabited___closed__6;
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
obj* l_Lean_ElabAttribute_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_ElabAttribute_Inhabited___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_mkElabAttribute___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::io_ref_get(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* _init_l_Lean_mkElabAttribute___rarg___lambda__2___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" elaborator attribute");
return x_1;
}
}
obj* l_Lean_mkElabAttribute___rarg___lambda__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_mkElabAttribute___rarg___lambda__2___closed__1;
x_4 = lean::string_append(x_1, x_3);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_mkElabAttribute___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(" elaborator");
return x_1;
}
}
obj* l_Lean_mkElabAttribute___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_9 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean::inc(x_2);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_10, 2, x_8);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set(x_10, 4, x_7);
x_11 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg(x_1, x_10, x_5);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_3);
x_15 = lean::string_append(x_3, x_14);
lean::inc(x_2);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_16, 0, x_2);
lean::inc(x_2);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_17, 0, x_2);
x_18 = l_Lean_AttributeImpl_inhabited___closed__1;
x_19 = l_Lean_AttributeImpl_inhabited___closed__4;
x_20 = l_Lean_AttributeImpl_inhabited___closed__5;
x_21 = 0;
x_22 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_18);
lean::cnstr_set(x_22, 3, x_16);
lean::cnstr_set(x_22, 4, x_17);
lean::cnstr_set(x_22, 5, x_19);
lean::cnstr_set(x_22, 6, x_20);
lean::cnstr_set(x_22, 7, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*8, x_21);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_3);
lean::cnstr_set(x_11, 0, x_23);
return x_11;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_24 = lean::cnstr_get(x_11, 0);
x_25 = lean::cnstr_get(x_11, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_11);
x_26 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_3);
x_27 = lean::string_append(x_3, x_26);
lean::inc(x_2);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_28, 0, x_2);
lean::inc(x_2);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_29, 0, x_2);
x_30 = l_Lean_AttributeImpl_inhabited___closed__1;
x_31 = l_Lean_AttributeImpl_inhabited___closed__4;
x_32 = l_Lean_AttributeImpl_inhabited___closed__5;
x_33 = 0;
x_34 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_34, 0, x_2);
lean::cnstr_set(x_34, 1, x_27);
lean::cnstr_set(x_34, 2, x_30);
lean::cnstr_set(x_34, 3, x_28);
lean::cnstr_set(x_34, 4, x_29);
lean::cnstr_set(x_34, 5, x_31);
lean::cnstr_set(x_34, 6, x_32);
lean::cnstr_set(x_34, 7, x_32);
lean::cnstr_set_scalar(x_34, sizeof(void*)*8, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_24);
lean::cnstr_set(x_35, 2, x_3);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_25);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_3);
lean::dec(x_2);
x_37 = !lean::is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_11, 0);
x_39 = lean::cnstr_get(x_11, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_11);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
}
obj* l_Lean_mkElabAttribute(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_mkElabAttribute___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_mkElabAttribute___rarg___lambda__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_mkElabAttribute___rarg___lambda__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_mkElabAttribute___rarg___lambda__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean::dec(x_8);
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
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_HashMap_Inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean::array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean::io_ref_reset(x_15, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_29 = x_21;
x_30 = lean::array_push(x_24, x_29);
x_31 = lean::io_ref_set(x_15, x_30, x_25);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_31, 0);
lean::dec(x_33);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_21);
x_36 = !lean::is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_31, 0);
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_31);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_25, 1);
lean::inc(x_40);
lean::dec(x_25);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_14);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_43 = x_21;
x_44 = lean::array_push(x_24, x_43);
x_45 = lean::io_ref_set(x_15, x_44, x_41);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_47 = x_45;
} else {
 lean::dec_ref(x_45);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_21);
lean::cnstr_set(x_48, 1, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_21);
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_51 = x_45;
} else {
 lean::dec_ref(x_45);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8 x_53; 
lean::dec(x_24);
lean::dec(x_21);
x_53 = !lean::is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_25, 0);
x_55 = lean::cnstr_get(x_25, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_25);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_22, 0);
x_58 = lean::cnstr_get(x_22, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_22);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_14);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::io_ref_reset(x_15, x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
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
lean::cnstr_set(x_63, 0, x_14);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_65 = x_21;
x_66 = lean::array_push(x_57, x_65);
x_67 = lean::io_ref_set(x_15, x_66, x_63);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_69 = x_67;
} else {
 lean::dec_ref(x_67);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_21);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_21);
x_71 = lean::cnstr_get(x_67, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_73 = x_67;
} else {
 lean::dec_ref(x_67);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
lean::dec(x_21);
x_75 = lean::cnstr_get(x_60, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_60, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_77 = x_60;
} else {
 lean::dec_ref(x_60);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8 x_79; 
lean::dec(x_21);
x_79 = !lean::is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_22, 0);
x_81 = lean::cnstr_get(x_22, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_22);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_83 = lean::cnstr_get(x_16, 0);
x_84 = lean::cnstr_get(x_16, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_16);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_14);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean::io_ref_get(x_15, x_85);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_14);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::io_ref_reset(x_15, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_95 = lean::cnstr_get(x_94, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_96 = x_94;
} else {
 lean::dec_ref(x_94);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_14);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_88);
x_99 = x_88;
x_100 = lean::array_push(x_90, x_99);
x_101 = lean::io_ref_set(x_15, x_100, x_97);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_103 = x_101;
} else {
 lean::dec_ref(x_101);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_88);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_88);
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_107 = x_101;
} else {
 lean::dec_ref(x_101);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_90);
lean::dec(x_88);
x_109 = lean::cnstr_get(x_94, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_94, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_111 = x_94;
} else {
 lean::dec_ref(x_94);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_88);
x_113 = lean::cnstr_get(x_89, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_89, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_115 = x_89;
} else {
 lean::dec_ref(x_89);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8 x_117; 
lean::dec(x_1);
x_117 = !lean::is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_16, 0);
x_119 = lean::cnstr_get(x_16, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_16);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_3, 1);
lean::inc(x_121);
lean::dec(x_3);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean::io_ref_get(x_124, x_123);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_128 = x_125;
} else {
 lean::dec_ref(x_125);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_122);
lean::cnstr_set(x_129, 1, x_127);
x_130 = lean::array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean::io_ref_get(x_124, x_129);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_122);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::io_ref_reset(x_124, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_140 = x_138;
} else {
 lean::dec_ref(x_138);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_122);
lean::cnstr_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_132);
x_143 = x_132;
x_144 = lean::array_push(x_134, x_143);
x_145 = lean::io_ref_set(x_124, x_144, x_141);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; 
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_147 = x_145;
} else {
 lean::dec_ref(x_145);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_132);
lean::cnstr_set(x_148, 1, x_146);
return x_148;
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_132);
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_151 = x_145;
} else {
 lean::dec_ref(x_145);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_150);
return x_152;
}
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
lean::dec(x_132);
x_153 = lean::cnstr_get(x_138, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_138, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_155 = x_138;
} else {
 lean::dec_ref(x_138);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_132);
x_157 = lean::cnstr_get(x_133, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_133, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_159 = x_133;
} else {
 lean::dec_ref(x_133);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
lean::cnstr_set(x_160, 1, x_158);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_1);
x_161 = lean::cnstr_get(x_125, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_125, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_163 = x_125;
} else {
 lean::dec_ref(x_125);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
lean::cnstr_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8 x_165; 
lean::dec(x_1);
x_165 = !lean::is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_3, 0);
x_167 = lean::cnstr_get(x_3, 1);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_3);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
return x_168;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3(x_1, x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_11 = l_Array_empty___closed__1;
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4(x_14, x_4);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_15, 0);
lean::cnstr_set(x_15, 0, x_9);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_1, 3);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_1, 4);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_10);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set(x_22, 4, x_20);
lean::cnstr_set(x_22, 5, x_21);
x_23 = lean::io_ref_get(x_3, x_15);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_23, 0, x_9);
x_26 = lean::io_ref_reset(x_3, x_23);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_26, 0);
lean::dec(x_28);
lean::cnstr_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_30 = x_22;
x_31 = lean::array_push(x_25, x_30);
x_32 = lean::io_ref_set(x_3, x_31, x_26);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_22);
return x_32;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_22);
x_37 = !lean::is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_32);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_26, 1);
lean::inc(x_41);
lean::dec(x_26);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_44 = x_22;
x_45 = lean::array_push(x_25, x_44);
x_46 = lean::io_ref_set(x_3, x_45, x_42);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_22);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_22);
x_50 = lean::cnstr_get(x_46, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_52 = x_46;
} else {
 lean::dec_ref(x_46);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8 x_54; 
lean::dec(x_25);
lean::dec(x_22);
x_54 = !lean::is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_26, 0);
x_56 = lean::cnstr_get(x_26, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_26);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_23, 0);
x_59 = lean::cnstr_get(x_23, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_23);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::io_ref_reset(x_3, x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_66 = x_22;
x_67 = lean::array_push(x_58, x_66);
x_68 = lean::io_ref_set(x_3, x_67, x_64);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_70 = x_68;
} else {
 lean::dec_ref(x_68);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_22);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_22);
x_72 = lean::cnstr_get(x_68, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_74 = x_68;
} else {
 lean::dec_ref(x_68);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_58);
lean::dec(x_22);
x_76 = lean::cnstr_get(x_61, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_61, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_78 = x_61;
} else {
 lean::dec_ref(x_61);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8 x_80; 
lean::dec(x_22);
x_80 = !lean::is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_23, 0);
x_82 = lean::cnstr_get(x_23, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_23);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_15, 0);
x_85 = lean::cnstr_get(x_15, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_15);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_9);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_1, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_1, 3);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_1, 4);
lean::inc(x_90);
lean::dec(x_1);
x_91 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_91, 0, x_84);
lean::cnstr_set(x_91, 1, x_87);
lean::cnstr_set(x_91, 2, x_10);
lean::cnstr_set(x_91, 3, x_88);
lean::cnstr_set(x_91, 4, x_89);
lean::cnstr_set(x_91, 5, x_90);
x_92 = lean::io_ref_get(x_3, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_9);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::io_ref_reset(x_3, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_99 = x_97;
} else {
 lean::dec_ref(x_97);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_9);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_91);
x_102 = x_91;
x_103 = lean::array_push(x_93, x_102);
x_104 = lean::io_ref_set(x_3, x_103, x_100);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; 
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_106 = x_104;
} else {
 lean::dec_ref(x_104);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_91);
lean::cnstr_set(x_107, 1, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_91);
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_110 = x_104;
} else {
 lean::dec_ref(x_104);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_93);
lean::dec(x_91);
x_112 = lean::cnstr_get(x_97, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_97, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_114 = x_97;
} else {
 lean::dec_ref(x_97);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_91);
x_116 = lean::cnstr_get(x_92, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_92, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_118 = x_92;
} else {
 lean::dec_ref(x_92);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8 x_120; 
lean::dec(x_10);
lean::dec(x_1);
x_120 = !lean::is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_15, 0);
x_122 = lean::cnstr_get(x_15, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_15);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_124 = lean::cnstr_get(x_1, 0);
lean::inc(x_124);
lean::dec(x_1);
x_125 = l_System_FilePath_dirName___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean::string_append(x_127, x_126);
lean::dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean::string_append(x_128, x_129);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_130);
return x_4;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_4, 0);
x_132 = lean::cnstr_get(x_4, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_4);
x_133 = lean::mk_nat_obj(0u);
x_134 = l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3(x_1, x_131, x_133);
lean::dec(x_131);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = lean::box(0);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_132);
x_137 = lean::cnstr_get(x_1, 1);
lean::inc(x_137);
x_138 = l_Array_empty___closed__1;
lean::inc(x_137);
x_139 = lean::apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_141, 0, x_139);
lean::closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4(x_141, x_136);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_135);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::cnstr_get(x_1, 0);
lean::inc(x_147);
x_148 = lean::cnstr_get(x_1, 2);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_1, 3);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_1, 4);
lean::inc(x_150);
lean::dec(x_1);
x_151 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_151, 0, x_143);
lean::cnstr_set(x_151, 1, x_147);
lean::cnstr_set(x_151, 2, x_137);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set(x_151, 4, x_149);
lean::cnstr_set(x_151, 5, x_150);
x_152 = lean::io_ref_get(x_3, x_146);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_152, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_155 = x_152;
} else {
 lean::dec_ref(x_152);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_135);
lean::cnstr_set(x_156, 1, x_154);
x_157 = lean::io_ref_reset(x_3, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_159 = x_157;
} else {
 lean::dec_ref(x_157);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_135);
lean::cnstr_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_151);
x_162 = x_151;
x_163 = lean::array_push(x_153, x_162);
x_164 = lean::io_ref_set(x_3, x_163, x_160);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_166; obj* x_167; 
x_165 = lean::cnstr_get(x_164, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_166 = x_164;
} else {
 lean::dec_ref(x_164);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_151);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_151);
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_170 = x_164;
} else {
 lean::dec_ref(x_164);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_153);
lean::dec(x_151);
x_172 = lean::cnstr_get(x_157, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_157, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_174 = x_157;
} else {
 lean::dec_ref(x_157);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
lean::cnstr_set(x_175, 1, x_173);
return x_175;
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_151);
x_176 = lean::cnstr_get(x_152, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_152, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_178 = x_152;
} else {
 lean::dec_ref(x_152);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set(x_179, 1, x_177);
return x_179;
}
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_137);
lean::dec(x_1);
x_180 = lean::cnstr_get(x_142, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_142, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_182 = x_142;
} else {
 lean::dec_ref(x_142);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
lean::cnstr_set(x_183, 1, x_181);
return x_183;
}
}
else
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_184 = lean::cnstr_get(x_1, 0);
lean::inc(x_184);
lean::dec(x_1);
x_185 = l_System_FilePath_dirName___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean::string_append(x_187, x_186);
lean::dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean::string_append(x_188, x_189);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8 x_192; 
lean::dec(x_1);
x_192 = !lean::is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
obj* x_193; obj* x_194; obj* x_195; 
x_193 = lean::cnstr_get(x_4, 0);
x_194 = lean::cnstr_get(x_4, 1);
lean::inc(x_194);
lean::inc(x_193);
lean::dec(x_4);
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set(x_195, 1, x_194);
return x_195;
}
}
}
}
obj* l_Lean_mkElabAttribute___at_Lean_mkTermElabAttribute___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_3);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_7);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_6);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__2(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_2);
x_14 = lean::string_append(x_2, x_13);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_15, 0, x_1);
lean::inc(x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__1;
x_18 = l_Lean_AttributeImpl_inhabited___closed__4;
x_19 = l_Lean_AttributeImpl_inhabited___closed__5;
x_20 = 0;
x_21 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_15);
lean::cnstr_set(x_21, 4, x_16);
lean::cnstr_set(x_21, 5, x_18);
lean::cnstr_set(x_21, 6, x_19);
lean::cnstr_set(x_21, 7, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*8, x_20);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_10, 0, x_22);
return x_10;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_23 = lean::cnstr_get(x_10, 0);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_10);
x_25 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_2);
x_26 = lean::string_append(x_2, x_25);
lean::inc(x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_27, 0, x_1);
lean::inc(x_1);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_28, 0, x_1);
x_29 = l_Lean_AttributeImpl_inhabited___closed__1;
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_26);
lean::cnstr_set(x_33, 2, x_29);
lean::cnstr_set(x_33, 3, x_27);
lean::cnstr_set(x_33, 4, x_28);
lean::cnstr_set(x_33, 5, x_30);
lean::cnstr_set(x_33, 6, x_31);
lean::cnstr_set(x_33, 7, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*8, x_32);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_23);
lean::cnstr_set(x_34, 2, x_2);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_24);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_2);
lean::dec(x_1);
x_36 = !lean::is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_10, 0);
x_38 = lean::cnstr_get(x_10, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_10);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
obj* _init_l_Lean_mkTermElabAttribute___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabTerm");
return x_1;
}
}
obj* _init_l_Lean_mkTermElabAttribute___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkTermElabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkTermElabAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkTermElabAttribute___closed__2;
x_3 = l_Lean_Parser_mkTermParserAttribute___closed__4;
x_4 = l_Lean_builtinTermElabTable;
x_5 = l_Lean_mkElabAttribute___at_Lean_mkTermElabAttribute___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_mkTermElabAttribute___spec__3(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_Lean_termElabAttribute___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
obj* _init_l_Lean_termElabAttribute___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = l_Lean_termElabAttribute___closed__1;
x_2 = lean::box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_3);
lean::cnstr_set(x_7, 3, x_4);
lean::cnstr_set(x_7, 4, x_5);
lean::cnstr_set(x_7, 5, x_6);
return x_7;
}
}
obj* _init_l_Lean_termElabAttribute___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_termElabAttribute___closed__2;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean::dec(x_8);
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
}
}
obj* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean::box(0);
lean::cnstr_set(x_3, 0, x_14);
x_15 = l___private_init_lean_environment_5__envExtensionsRef;
x_16 = lean::io_ref_get(x_15, x_3);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_16, 0, x_14);
x_19 = lean::array_get_size(x_18);
lean::dec(x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::io_ref_get(x_15, x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_14);
x_25 = lean::io_ref_reset(x_15, x_22);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_25, 0);
lean::dec(x_27);
lean::cnstr_set(x_25, 0, x_14);
x_28 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_29 = x_21;
x_30 = lean::array_push(x_24, x_29);
x_31 = lean::io_ref_set(x_15, x_30, x_25);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::cnstr_get(x_31, 0);
lean::dec(x_33);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_21);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_21);
x_36 = !lean::is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_31, 0);
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_31);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_25, 1);
lean::inc(x_40);
lean::dec(x_25);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_14);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_43 = x_21;
x_44 = lean::array_push(x_24, x_43);
x_45 = lean::io_ref_set(x_15, x_44, x_41);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_47 = x_45;
} else {
 lean::dec_ref(x_45);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_21);
lean::cnstr_set(x_48, 1, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_21);
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_45, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_51 = x_45;
} else {
 lean::dec_ref(x_45);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8 x_53; 
lean::dec(x_24);
lean::dec(x_21);
x_53 = !lean::is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_25, 0);
x_55 = lean::cnstr_get(x_25, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_25);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_22, 0);
x_58 = lean::cnstr_get(x_22, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_22);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_14);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::io_ref_reset(x_15, x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
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
lean::cnstr_set(x_63, 0, x_14);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_21);
x_65 = x_21;
x_66 = lean::array_push(x_57, x_65);
x_67 = lean::io_ref_set(x_15, x_66, x_63);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_67, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_69 = x_67;
} else {
 lean::dec_ref(x_67);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_21);
lean::cnstr_set(x_70, 1, x_68);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_21);
x_71 = lean::cnstr_get(x_67, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 1);
 x_73 = x_67;
} else {
 lean::dec_ref(x_67);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
lean::dec(x_21);
x_75 = lean::cnstr_get(x_60, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_60, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_77 = x_60;
} else {
 lean::dec_ref(x_60);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8 x_79; 
lean::dec(x_21);
x_79 = !lean::is_exclusive(x_22);
if (x_79 == 0)
{
return x_22;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_22, 0);
x_81 = lean::cnstr_get(x_22, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_22);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_83 = lean::cnstr_get(x_16, 0);
x_84 = lean::cnstr_get(x_16, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_16);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_14);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::array_get_size(x_83);
lean::dec(x_83);
x_87 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean::io_ref_get(x_15, x_85);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_14);
lean::cnstr_set(x_93, 1, x_91);
x_94 = lean::io_ref_reset(x_15, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_95 = lean::cnstr_get(x_94, 1);
lean::inc(x_95);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_96 = x_94;
} else {
 lean::dec_ref(x_94);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_14);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_88);
x_99 = x_88;
x_100 = lean::array_push(x_90, x_99);
x_101 = lean::io_ref_set(x_15, x_100, x_97);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; 
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_103 = x_101;
} else {
 lean::dec_ref(x_101);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_88);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_88);
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_101, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_107 = x_101;
} else {
 lean::dec_ref(x_101);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
return x_108;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_90);
lean::dec(x_88);
x_109 = lean::cnstr_get(x_94, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_94, 1);
lean::inc(x_110);
if (lean::is_exclusive(x_94)) {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_111 = x_94;
} else {
 lean::dec_ref(x_94);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_110);
return x_112;
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_88);
x_113 = lean::cnstr_get(x_89, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_89, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_115 = x_89;
} else {
 lean::dec_ref(x_89);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8 x_117; 
lean::dec(x_1);
x_117 = !lean::is_exclusive(x_16);
if (x_117 == 0)
{
return x_16;
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_16, 0);
x_119 = lean::cnstr_get(x_16, 1);
lean::inc(x_119);
lean::inc(x_118);
lean::dec(x_16);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_3, 1);
lean::inc(x_121);
lean::dec(x_3);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
x_124 = l___private_init_lean_environment_5__envExtensionsRef;
x_125 = lean::io_ref_get(x_124, x_123);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_128 = x_125;
} else {
 lean::dec_ref(x_125);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_122);
lean::cnstr_set(x_129, 1, x_127);
x_130 = lean::array_get_size(x_126);
lean::dec(x_126);
x_131 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2;
x_132 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_131);
x_133 = lean::io_ref_get(x_124, x_129);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_122);
lean::cnstr_set(x_137, 1, x_135);
x_138 = lean::io_ref_reset(x_124, x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_140 = x_138;
} else {
 lean::dec_ref(x_138);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_122);
lean::cnstr_set(x_141, 1, x_139);
x_142 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_132);
x_143 = x_132;
x_144 = lean::array_push(x_134, x_143);
x_145 = lean::io_ref_set(x_124, x_144, x_141);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; obj* x_147; obj* x_148; 
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_147 = x_145;
} else {
 lean::dec_ref(x_145);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_132);
lean::cnstr_set(x_148, 1, x_146);
return x_148;
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_132);
x_149 = lean::cnstr_get(x_145, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_145, 1);
lean::inc(x_150);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_151 = x_145;
} else {
 lean::dec_ref(x_145);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
lean::cnstr_set(x_152, 1, x_150);
return x_152;
}
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_134);
lean::dec(x_132);
x_153 = lean::cnstr_get(x_138, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_138, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_155 = x_138;
} else {
 lean::dec_ref(x_138);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set(x_156, 1, x_154);
return x_156;
}
}
else
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_132);
x_157 = lean::cnstr_get(x_133, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_133, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_159 = x_133;
} else {
 lean::dec_ref(x_133);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
lean::cnstr_set(x_160, 1, x_158);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_1);
x_161 = lean::cnstr_get(x_125, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_125, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_163 = x_125;
} else {
 lean::dec_ref(x_125);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
lean::cnstr_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8 x_165; 
lean::dec(x_1);
x_165 = !lean::is_exclusive(x_3);
if (x_165 == 0)
{
return x_3;
}
else
{
obj* x_166; obj* x_167; obj* x_168; 
x_166 = lean::cnstr_get(x_3, 0);
x_167 = lean::cnstr_get(x_3, 1);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_3);
x_168 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
return x_168;
}
}
}
}
obj* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_environment_8__persistentEnvExtensionsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3(x_1, x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_11 = l_Array_empty___closed__1;
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__4(x_14, x_4);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_15, 0);
lean::cnstr_set(x_15, 0, x_9);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_1, 3);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_1, 4);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_10);
lean::cnstr_set(x_22, 3, x_19);
lean::cnstr_set(x_22, 4, x_20);
lean::cnstr_set(x_22, 5, x_21);
x_23 = lean::io_ref_get(x_3, x_15);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_23, 0);
lean::cnstr_set(x_23, 0, x_9);
x_26 = lean::io_ref_reset(x_3, x_23);
if (lean::obj_tag(x_26) == 0)
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_26, 0);
lean::dec(x_28);
lean::cnstr_set(x_26, 0, x_9);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_30 = x_22;
x_31 = lean::array_push(x_25, x_30);
x_32 = lean::io_ref_set(x_3, x_31, x_26);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
lean::cnstr_set(x_32, 0, x_22);
return x_32;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_22);
x_37 = !lean::is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_32, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_32);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_26, 1);
lean::inc(x_41);
lean::dec(x_26);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_44 = x_22;
x_45 = lean::array_push(x_25, x_44);
x_46 = lean::io_ref_set(x_3, x_45, x_42);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_48 = x_46;
} else {
 lean::dec_ref(x_46);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_22);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_22);
x_50 = lean::cnstr_get(x_46, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_52 = x_46;
} else {
 lean::dec_ref(x_46);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8 x_54; 
lean::dec(x_25);
lean::dec(x_22);
x_54 = !lean::is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_26, 0);
x_56 = lean::cnstr_get(x_26, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_26);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_23, 0);
x_59 = lean::cnstr_get(x_23, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_23);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_9);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::io_ref_reset(x_3, x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_62);
x_65 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_22);
x_66 = x_22;
x_67 = lean::array_push(x_58, x_66);
x_68 = lean::io_ref_set(x_3, x_67, x_64);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = lean::cnstr_get(x_68, 1);
lean::inc(x_69);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_70 = x_68;
} else {
 lean::dec_ref(x_68);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_22);
lean::cnstr_set(x_71, 1, x_69);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_22);
x_72 = lean::cnstr_get(x_68, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_74 = x_68;
} else {
 lean::dec_ref(x_68);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_58);
lean::dec(x_22);
x_76 = lean::cnstr_get(x_61, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_61, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_78 = x_61;
} else {
 lean::dec_ref(x_61);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8 x_80; 
lean::dec(x_22);
x_80 = !lean::is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_23, 0);
x_82 = lean::cnstr_get(x_23, 1);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_23);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_15, 0);
x_85 = lean::cnstr_get(x_15, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_15);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_9);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_1, 2);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_1, 3);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_1, 4);
lean::inc(x_90);
lean::dec(x_1);
x_91 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_91, 0, x_84);
lean::cnstr_set(x_91, 1, x_87);
lean::cnstr_set(x_91, 2, x_10);
lean::cnstr_set(x_91, 3, x_88);
lean::cnstr_set(x_91, 4, x_89);
lean::cnstr_set(x_91, 5, x_90);
x_92 = lean::io_ref_get(x_3, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_9);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::io_ref_reset(x_3, x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_99 = x_97;
} else {
 lean::dec_ref(x_97);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_9);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_91);
x_102 = x_91;
x_103 = lean::array_push(x_93, x_102);
x_104 = lean::io_ref_set(x_3, x_103, x_100);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; obj* x_107; 
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_106 = x_104;
} else {
 lean::dec_ref(x_104);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_91);
lean::cnstr_set(x_107, 1, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_91);
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_104, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_110 = x_104;
} else {
 lean::dec_ref(x_104);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_93);
lean::dec(x_91);
x_112 = lean::cnstr_get(x_97, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_97, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_114 = x_97;
} else {
 lean::dec_ref(x_97);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_91);
x_116 = lean::cnstr_get(x_92, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_92, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_118 = x_92;
} else {
 lean::dec_ref(x_92);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8 x_120; 
lean::dec(x_10);
lean::dec(x_1);
x_120 = !lean::is_exclusive(x_15);
if (x_120 == 0)
{
return x_15;
}
else
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = lean::cnstr_get(x_15, 0);
x_122 = lean::cnstr_get(x_15, 1);
lean::inc(x_122);
lean::inc(x_121);
lean::dec(x_15);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_124 = lean::cnstr_get(x_1, 0);
lean::inc(x_124);
lean::dec(x_1);
x_125 = l_System_FilePath_dirName___closed__1;
x_126 = l_Lean_Name_toStringWithSep___main(x_125, x_124);
x_127 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_128 = lean::string_append(x_127, x_126);
lean::dec(x_126);
x_129 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_130 = lean::string_append(x_128, x_129);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_130);
return x_4;
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; uint8 x_134; 
x_131 = lean::cnstr_get(x_4, 0);
x_132 = lean::cnstr_get(x_4, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_4);
x_133 = lean::mk_nat_obj(0u);
x_134 = l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3(x_1, x_131, x_133);
lean::dec(x_131);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = lean::box(0);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_132);
x_137 = lean::cnstr_get(x_1, 1);
lean::inc(x_137);
x_138 = l_Array_empty___closed__1;
lean::inc(x_137);
x_139 = lean::apply_1(x_137, x_138);
x_140 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_141 = lean::alloc_closure(reinterpret_cast<void*>(l_EState_bind___rarg), 3, 2);
lean::closure_set(x_141, 0, x_139);
lean::closure_set(x_141, 1, x_140);
x_142 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__4(x_141, x_136);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_135);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::cnstr_get(x_1, 0);
lean::inc(x_147);
x_148 = lean::cnstr_get(x_1, 2);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_1, 3);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_1, 4);
lean::inc(x_150);
lean::dec(x_1);
x_151 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_151, 0, x_143);
lean::cnstr_set(x_151, 1, x_147);
lean::cnstr_set(x_151, 2, x_137);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set(x_151, 4, x_149);
lean::cnstr_set(x_151, 5, x_150);
x_152 = lean::io_ref_get(x_3, x_146);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_152, 1);
lean::inc(x_154);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_155 = x_152;
} else {
 lean::dec_ref(x_152);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_135);
lean::cnstr_set(x_156, 1, x_154);
x_157 = lean::io_ref_reset(x_3, x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
x_158 = lean::cnstr_get(x_157, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_159 = x_157;
} else {
 lean::dec_ref(x_157);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_135);
lean::cnstr_set(x_160, 1, x_158);
x_161 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean::inc(x_151);
x_162 = x_151;
x_163 = lean::array_push(x_153, x_162);
x_164 = lean::io_ref_set(x_3, x_163, x_160);
if (lean::obj_tag(x_164) == 0)
{
obj* x_165; obj* x_166; obj* x_167; 
x_165 = lean::cnstr_get(x_164, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_166 = x_164;
} else {
 lean::dec_ref(x_164);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_151);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_151);
x_168 = lean::cnstr_get(x_164, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_164, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_170 = x_164;
} else {
 lean::dec_ref(x_164);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_153);
lean::dec(x_151);
x_172 = lean::cnstr_get(x_157, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_157, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_157)) {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_174 = x_157;
} else {
 lean::dec_ref(x_157);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
lean::cnstr_set(x_175, 1, x_173);
return x_175;
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_151);
x_176 = lean::cnstr_get(x_152, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_152, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 x_178 = x_152;
} else {
 lean::dec_ref(x_152);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set(x_179, 1, x_177);
return x_179;
}
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_137);
lean::dec(x_1);
x_180 = lean::cnstr_get(x_142, 0);
lean::inc(x_180);
x_181 = lean::cnstr_get(x_142, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_182 = x_142;
} else {
 lean::dec_ref(x_142);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_180);
lean::cnstr_set(x_183, 1, x_181);
return x_183;
}
}
else
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_184 = lean::cnstr_get(x_1, 0);
lean::inc(x_184);
lean::dec(x_1);
x_185 = l_System_FilePath_dirName___closed__1;
x_186 = l_Lean_Name_toStringWithSep___main(x_185, x_184);
x_187 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_188 = lean::string_append(x_187, x_186);
lean::dec(x_186);
x_189 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_190 = lean::string_append(x_188, x_189);
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_132);
return x_191;
}
}
}
else
{
uint8 x_192; 
lean::dec(x_1);
x_192 = !lean::is_exclusive(x_4);
if (x_192 == 0)
{
return x_4;
}
else
{
obj* x_193; obj* x_194; obj* x_195; 
x_193 = lean::cnstr_get(x_4, 0);
x_194 = lean::cnstr_get(x_4, 1);
lean::inc(x_194);
lean::inc(x_193);
lean::dec(x_4);
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_193);
lean::cnstr_set(x_195, 1, x_194);
return x_195;
}
}
}
}
obj* l_Lean_mkElabAttribute___at_Lean_mkCommandElabAttribute___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_3);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_7);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_6);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_mkCommandElabAttribute___spec__2(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_2);
x_14 = lean::string_append(x_2, x_13);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_15, 0, x_1);
lean::inc(x_1);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__1;
x_18 = l_Lean_AttributeImpl_inhabited___closed__4;
x_19 = l_Lean_AttributeImpl_inhabited___closed__5;
x_20 = 0;
x_21 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_15);
lean::cnstr_set(x_21, 4, x_16);
lean::cnstr_set(x_21, 5, x_18);
lean::cnstr_set(x_21, 6, x_19);
lean::cnstr_set(x_21, 7, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*8, x_20);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_10, 0, x_22);
return x_10;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_23 = lean::cnstr_get(x_10, 0);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_10);
x_25 = l_Lean_mkElabAttribute___rarg___closed__1;
lean::inc(x_2);
x_26 = lean::string_append(x_2, x_25);
lean::inc(x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean::closure_set(x_27, 0, x_1);
lean::inc(x_1);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_28, 0, x_1);
x_29 = l_Lean_AttributeImpl_inhabited___closed__1;
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_26);
lean::cnstr_set(x_33, 2, x_29);
lean::cnstr_set(x_33, 3, x_27);
lean::cnstr_set(x_33, 4, x_28);
lean::cnstr_set(x_33, 5, x_30);
lean::cnstr_set(x_33, 6, x_31);
lean::cnstr_set(x_33, 7, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*8, x_32);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_23);
lean::cnstr_set(x_34, 2, x_2);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_24);
return x_35;
}
}
else
{
uint8 x_36; 
lean::dec(x_2);
lean::dec(x_1);
x_36 = !lean::is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_10, 0);
x_38 = lean::cnstr_get(x_10, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_10);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
obj* _init_l_Lean_mkCommandElabAttribute___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("commandTerm");
return x_1;
}
}
obj* _init_l_Lean_mkCommandElabAttribute___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_mkCommandElabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkCommandElabAttribute(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_mkCommandElabAttribute___closed__2;
x_3 = l_Lean_Parser_mkCommandParserAttribute___closed__4;
x_4 = l_Lean_builtinCommandElabTable;
x_5 = l_Lean_mkElabAttribute___at_Lean_mkCommandElabAttribute___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_mkCommandElabAttribute___spec__3(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Lean_mkMessage(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
x_10 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
x_12 = l_Lean_FileMap_toPosition___main(x_9, x_11);
lean::dec(x_11);
x_13 = 2;
x_14 = l_String_splitAux___main___closed__1;
lean::inc(x_8);
x_15 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_14);
lean::cnstr_set(x_15, 4, x_1);
lean::cnstr_set_scalar(x_15, sizeof(void*)*5, x_13);
lean::cnstr_set(x_4, 0, x_15);
return x_4;
}
else
{
obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_2, 0);
x_17 = l_Lean_FileMap_toPosition___main(x_9, x_16);
x_18 = 2;
x_19 = l_String_splitAux___main___closed__1;
lean::inc(x_8);
x_20 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_10);
lean::cnstr_set(x_20, 3, x_19);
lean::cnstr_set(x_20, 4, x_1);
lean::cnstr_set_scalar(x_20, sizeof(void*)*5, x_18);
lean::cnstr_set(x_4, 0, x_20);
return x_4;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 1);
x_24 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_21, 2);
lean::inc(x_25);
x_26 = l_Lean_FileMap_toPosition___main(x_23, x_25);
lean::dec(x_25);
x_27 = 2;
x_28 = l_String_splitAux___main___closed__1;
lean::inc(x_22);
x_29 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set(x_29, 2, x_24);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set(x_29, 4, x_1);
lean::cnstr_set_scalar(x_29, sizeof(void*)*5, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_21);
return x_30;
}
else
{
obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_2, 0);
x_32 = l_Lean_FileMap_toPosition___main(x_23, x_31);
x_33 = 2;
x_34 = l_String_splitAux___main___closed__1;
lean::inc(x_22);
x_35 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_32);
lean::cnstr_set(x_35, 2, x_24);
lean::cnstr_set(x_35, 3, x_34);
lean::cnstr_set(x_35, 4, x_1);
lean::cnstr_set_scalar(x_35, sizeof(void*)*5, x_33);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_21);
return x_36;
}
}
}
}
obj* l_Lean_mkMessage___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_mkMessage(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_logErrorAt(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = l_Lean_mkMessage(x_2, x_5, x_3, x_4);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_6, 1);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set(x_8, 1, x_12);
x_13 = lean::box(0);
lean::cnstr_set(x_6, 0, x_13);
return x_6;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_6, 0);
x_15 = lean::cnstr_get(x_8, 0);
x_16 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
x_18 = lean::cnstr_get(x_8, 3);
x_19 = lean::cnstr_get(x_8, 4);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_8);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_14);
lean::cnstr_set(x_20, 1, x_16);
x_21 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_21, 0, x_15);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_18);
lean::cnstr_set(x_21, 4, x_19);
x_22 = lean::box(0);
lean::cnstr_set(x_6, 1, x_21);
lean::cnstr_set(x_6, 0, x_22);
return x_6;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_23 = lean::cnstr_get(x_6, 1);
x_24 = lean::cnstr_get(x_6, 0);
lean::inc(x_23);
lean::inc(x_24);
lean::dec(x_6);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_23, 2);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_23, 3);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_23, 4);
lean::inc(x_29);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 lean::cnstr_release(x_23, 2);
 lean::cnstr_release(x_23, 3);
 lean::cnstr_release(x_23, 4);
 x_30 = x_23;
} else {
 lean::dec_ref(x_23);
 x_30 = lean::box(0);
}
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_24);
lean::cnstr_set(x_31, 1, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set(x_32, 2, x_27);
lean::cnstr_set(x_32, 3, x_28);
lean::cnstr_set(x_32, 4, x_29);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_6);
if (x_35 == 0)
{
return x_6;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_6, 0);
x_37 = lean::cnstr_get(x_6, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_6);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
}
obj* l_Lean_logErrorAt___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_logErrorAt(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_logErrorUsingCmdPos(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::box(0);
lean::inc(x_5);
lean::cnstr_set(x_3, 0, x_7);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_9 = l_Lean_logErrorAt(x_8, x_1, x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::box(0);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::cnstr_get(x_10, 2);
lean::inc(x_13);
lean::dec(x_10);
x_14 = l_Lean_logErrorAt(x_13, x_1, x_2, x_12);
return x_14;
}
}
}
obj* l_Lean_logErrorUsingCmdPos___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_logErrorUsingCmdPos(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_getPos(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_getPos___rarg(x_1);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_6, 2);
lean::inc(x_8);
lean::cnstr_set(x_3, 0, x_8);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_9, 2);
lean::inc(x_10);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
lean::dec(x_4);
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_3, 0);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_12);
return x_3;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_12);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_Lean_getPos___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getPos(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_logError(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_getPos(x_1, x_3, x_4);
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
x_9 = l_Lean_logErrorAt(x_7, x_2, x_3, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_5);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_Lean_logErrorAt(x_10, x_2, x_3, x_13);
return x_14;
}
}
else
{
uint8 x_15; 
lean::dec(x_2);
x_15 = !lean::is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_5, 0);
x_17 = lean::cnstr_get(x_5, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_5);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_Lean_logError___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_logError(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_toMessage___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
lean::cnstr_set(x_3, 0, x_4);
return x_3;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::box(0);
x_11 = l_Lean_mkMessage(x_9, x_10, x_2, x_3);
return x_11;
}
}
}
obj* l_Lean_toMessage___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_toMessage___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_toMessage(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_toMessage___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_toMessage___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_toMessage(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_logElabException(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_toMessage___main(x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_6, 1, x_10);
x_11 = lean::box(0);
lean::cnstr_set(x_4, 0, x_11);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_4, 0);
x_13 = lean::cnstr_get(x_6, 0);
x_14 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
x_16 = lean::cnstr_get(x_6, 3);
x_17 = lean::cnstr_get(x_6, 4);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_6);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_14);
x_19 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set(x_19, 2, x_15);
lean::cnstr_set(x_19, 3, x_16);
lean::cnstr_set(x_19, 4, x_17);
x_20 = lean::box(0);
lean::cnstr_set(x_4, 1, x_19);
lean::cnstr_set(x_4, 0, x_20);
return x_4;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_21 = lean::cnstr_get(x_4, 1);
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
lean::inc(x_22);
lean::dec(x_4);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_21, 2);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_21, 3);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_21, 4);
lean::inc(x_27);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 lean::cnstr_release(x_21, 2);
 lean::cnstr_release(x_21, 3);
 lean::cnstr_release(x_21, 4);
 x_28 = x_21;
} else {
 lean::dec_ref(x_21);
 x_28 = lean::box(0);
}
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set(x_29, 1, x_24);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_23);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set(x_30, 2, x_25);
lean::cnstr_set(x_30, 3, x_26);
lean::cnstr_set(x_30, 4, x_27);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_4);
if (x_33 == 0)
{
return x_4;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_4, 0);
x_35 = lean::cnstr_get(x_4, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_4);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
}
obj* l_Lean_logElabException___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_logElabException(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_logErrorAndThrow___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_Lean_logError(x_1, x_2, x_3, x_4);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::dec(x_7);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_2);
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
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_2);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
lean::dec(x_2);
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_5, 0);
x_14 = lean::cnstr_get(x_5, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_5);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_Lean_logErrorAndThrow(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_logErrorAndThrow___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_logErrorAndThrow___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_logErrorAndThrow___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* _init_l_Lean_logUnknownDecl___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown declaration '");
return x_1;
}
}
obj* l_Lean_logUnknownDecl(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = l_System_FilePath_dirName___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = l_Lean_logUnknownDecl___closed__1;
x_8 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean::string_append(x_8, x_9);
x_11 = l_Lean_logError(x_1, x_10, x_3, x_4);
return x_11;
}
}
obj* l_Lean_logUnknownDecl___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_logUnknownDecl(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_getEnv___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 0);
lean::dec(x_4);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::cnstr_set(x_1, 0, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
}
obj* l_Lean_getEnv(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_getEnv___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_getEnv___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getEnv(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_find___main___at_Lean_elabTerm___spec__3(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_find___at_Lean_elabTerm___spec__2(obj* x_1, obj* x_2) {
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
x_10 = l_AssocList_find___main___at_Lean_elabTerm___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_addBuiltinTermElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_HashMapImp_find___at_Lean_elabTerm___spec__2(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_elabTerm___spec__2(x_8, x_2);
return x_9;
}
}
}
obj* _init_l_Lean_elabTerm___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
obj* _init_l_Lean_elabTerm___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_elabTerm___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_elabTerm___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("term elaborator failed, no support for syntax '");
return x_1;
}
}
obj* l_Lean_elabTerm(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::inc(x_6);
lean::cnstr_set(x_3, 0, x_8);
x_9 = l_Lean_termElabAttribute;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_12 = l_Lean_PersistentEnvExtension_getState___rarg(x_10, x_11);
lean::dec(x_11);
x_13 = l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1(x_12, x_4);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_4);
x_16 = l_Lean_elabTerm___closed__3;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_18 = l_Char_HasRepr___closed__1;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Lean_logErrorAndThrow___rarg(x_1, x_19, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_22 = lean::apply_3(x_21, x_1, x_2, x_3);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::dec(x_3);
x_24 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = l_Lean_termElabAttribute;
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_29 = l_Lean_PersistentEnvExtension_getState___rarg(x_27, x_28);
lean::dec(x_28);
x_30 = l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1(x_29, x_4);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_4);
x_33 = l_Lean_elabTerm___closed__3;
x_34 = lean::string_append(x_33, x_32);
lean::dec(x_32);
x_35 = l_Char_HasRepr___closed__1;
x_36 = lean::string_append(x_34, x_35);
x_37 = l_Lean_logErrorAndThrow___rarg(x_1, x_36, x_2, x_25);
lean::dec(x_2);
lean::dec(x_1);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_4);
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_39 = lean::apply_3(x_38, x_1, x_2, x_25);
return x_39;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_2);
lean::dec(x_1);
x_40 = !lean::is_exclusive(x_3);
if (x_40 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_3, 0);
lean::dec(x_41);
x_42 = l_Lean_elabTerm___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_42);
return x_3;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_3, 1);
lean::inc(x_43);
lean::dec(x_3);
x_44 = l_Lean_elabTerm___closed__2;
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_elabTerm___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_elabTerm___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_elabTerm___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_elabTerm___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___main___at_Lean_elabTerm___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_AssocList_find___main___at_Lean_elabCommand___spec__3(obj* x_1, obj* x_2) {
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
obj* l_HashMapImp_find___at_Lean_elabCommand___spec__2(obj* x_1, obj* x_2) {
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
x_10 = l_AssocList_find___main___at_Lean_elabCommand___spec__3(x_2, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_RBNode_find___main___at_Lean_addBuiltinCommandElab___spec__4(x_5, x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_HashMapImp_find___at_Lean_elabCommand___spec__2(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_elabCommand___spec__2(x_8, x_2);
return x_9;
}
}
}
obj* _init_l_Lean_elabCommand___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected command");
return x_1;
}
}
obj* _init_l_Lean_elabCommand___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("command '");
return x_1;
}
}
obj* _init_l_Lean_elabCommand___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' has not been implemented");
return x_1;
}
}
obj* l_Lean_elabCommand(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::inc(x_6);
lean::cnstr_set(x_3, 0, x_8);
x_9 = l_Lean_commandElabAttribute;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_12 = l_Lean_PersistentEnvExtension_getState___rarg(x_10, x_11);
lean::dec(x_11);
x_13 = l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1(x_12, x_4);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_4);
x_16 = l_Lean_elabCommand___closed__2;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_18 = l_Lean_elabCommand___closed__3;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Lean_logError(x_1, x_19, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
lean::dec(x_13);
x_22 = lean::apply_3(x_21, x_1, x_2, x_3);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::dec(x_3);
x_24 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
x_26 = l_Lean_commandElabAttribute;
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
lean::dec(x_23);
x_29 = l_Lean_PersistentEnvExtension_getState___rarg(x_27, x_28);
lean::dec(x_28);
x_30 = l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1(x_29, x_4);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_4);
x_33 = l_Lean_elabCommand___closed__2;
x_34 = lean::string_append(x_33, x_32);
lean::dec(x_32);
x_35 = l_Lean_elabCommand___closed__3;
x_36 = lean::string_append(x_34, x_35);
x_37 = l_Lean_logError(x_1, x_36, x_2, x_25);
lean::dec(x_2);
lean::dec(x_1);
return x_37;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_4);
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_39 = lean::apply_3(x_38, x_1, x_2, x_25);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; 
lean::dec(x_1);
x_40 = l_Lean_elabCommand___closed__1;
x_41 = l_Lean_logErrorUsingCmdPos(x_40, x_2, x_3);
lean::dec(x_2);
return x_41;
}
}
}
obj* l_AssocList_find___main___at_Lean_elabCommand___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_AssocList_find___main___at_Lean_elabCommand___spec__3(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_HashMapImp_find___at_Lean_elabCommand___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_find___at_Lean_elabCommand___spec__2(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_find___main___at_Lean_elabCommand___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getElabContext(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
}
}
obj* l_Lean_getElabContext___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getElabContext(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_runElab___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getElabContext(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_6, 0);
x_10 = lean::box(0);
lean::cnstr_set(x_4, 1, x_9);
lean::cnstr_set(x_4, 0, x_10);
x_11 = lean::apply_2(x_1, x_8, x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_13);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_15);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_11);
if (x_17 == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_18);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_11, 0);
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_20);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get(x_6, 0);
x_24 = lean::cnstr_get(x_6, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_6);
x_25 = lean::box(0);
lean::cnstr_set(x_4, 1, x_23);
lean::cnstr_set(x_4, 0, x_25);
x_26 = lean::apply_2(x_1, x_22, x_4);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_29 = x_26;
} else {
 lean::dec_ref(x_26);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_24);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_34 = x_26;
} else {
 lean::dec_ref(x_26);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_24);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 1);
x_38 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::inc(x_38);
lean::dec(x_4);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_41 = x_37;
} else {
 lean::dec_ref(x_37);
 x_41 = lean::box(0);
}
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
x_44 = lean::apply_2(x_1, x_38, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_41;
}
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_40);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_52 = x_44;
} else {
 lean::dec_ref(x_44);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_41;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_40);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_1);
x_55 = !lean::is_exclusive(x_4);
if (x_55 == 0)
{
return x_4;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_4, 0);
x_57 = lean::cnstr_get(x_4, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_4);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
}
obj* l_Lean_runElab(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_runElab___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_runElab___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_runElab___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getElabContext(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_6, 0);
x_10 = lean::box(0);
lean::cnstr_set(x_4, 1, x_9);
lean::cnstr_set(x_4, 0, x_10);
x_11 = l_Lean_elabCommand(x_1, x_8, x_4);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_13);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_15);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_11);
if (x_17 == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_18);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_11, 0);
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_20);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get(x_6, 0);
x_24 = lean::cnstr_get(x_6, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_6);
x_25 = lean::box(0);
lean::cnstr_set(x_4, 1, x_23);
lean::cnstr_set(x_4, 0, x_25);
x_26 = l_Lean_elabCommand(x_1, x_22, x_4);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_29 = x_26;
} else {
 lean::dec_ref(x_26);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_24);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_34 = x_26;
} else {
 lean::dec_ref(x_26);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_24);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 1);
x_38 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::inc(x_38);
lean::dec(x_4);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_41 = x_37;
} else {
 lean::dec_ref(x_37);
 x_41 = lean::box(0);
}
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
x_44 = l_Lean_elabCommand(x_1, x_38, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_41;
}
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_40);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_52 = x_44;
} else {
 lean::dec_ref(x_44);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_41;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_40);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_1);
x_55 = !lean::is_exclusive(x_4);
if (x_55 == 0)
{
return x_4;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_4, 0);
x_57 = lean::cnstr_get(x_4, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_4);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
}
obj* l_Lean_elabCommandAtFrontend(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_elabCommandAtFrontend___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_elabCommandAtFrontend(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_updateCmdPos___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 0);
lean::dec(x_4);
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_3, 1);
x_9 = lean::cnstr_get(x_6, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::cnstr_set(x_6, 2, x_10);
x_11 = lean::box(0);
lean::cnstr_set(x_1, 0, x_11);
return x_1;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_6, 0);
x_14 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 3);
x_16 = lean::cnstr_get(x_6, 4);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_6);
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set(x_18, 2, x_17);
lean::cnstr_set(x_18, 3, x_15);
lean::cnstr_set(x_18, 4, x_16);
lean::cnstr_set(x_3, 0, x_18);
x_19 = lean::box(0);
lean::cnstr_set(x_1, 0, x_19);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_3, 0);
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_3);
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_20, 3);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_20, 4);
lean::inc(x_25);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 lean::cnstr_release(x_20, 2);
 lean::cnstr_release(x_20, 3);
 lean::cnstr_release(x_20, 4);
 x_26 = x_20;
} else {
 lean::dec_ref(x_20);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_21, 0);
lean::inc(x_27);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_22);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
lean::cnstr_set(x_28, 3, x_24);
lean::cnstr_set(x_28, 4, x_25);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_21);
x_30 = lean::box(0);
lean::cnstr_set(x_1, 1, x_29);
lean::cnstr_set(x_1, 0, x_30);
return x_1;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_31 = lean::cnstr_get(x_1, 1);
lean::inc(x_31);
lean::dec(x_1);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_34 = x_31;
} else {
 lean::dec_ref(x_31);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_32, 1);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_32, 3);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_32, 4);
lean::inc(x_38);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 lean::cnstr_release(x_32, 2);
 lean::cnstr_release(x_32, 3);
 lean::cnstr_release(x_32, 4);
 x_39 = x_32;
} else {
 lean::dec_ref(x_32);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
if (lean::is_scalar(x_39)) {
 x_41 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_41 = x_39;
}
lean::cnstr_set(x_41, 0, x_35);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_40);
lean::cnstr_set(x_41, 3, x_37);
lean::cnstr_set(x_41, 4, x_38);
if (lean::is_scalar(x_34)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_34;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_33);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_42);
return x_44;
}
}
}
obj* l_Lean_updateCmdPos(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_updateCmdPos___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_updateCmdPos___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_updateCmdPos(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_runElab___at_Lean_processCommand___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_getElabContext(x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 1);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_6, 0);
x_10 = lean::box(0);
lean::cnstr_set(x_4, 1, x_9);
lean::cnstr_set(x_4, 0, x_10);
x_11 = l_Lean_logElabException(x_1, x_8, x_4);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_13);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_11, 0);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_15);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_6);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_11);
if (x_17 == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_11, 1);
lean::cnstr_set(x_6, 0, x_18);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_11, 0);
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_11);
lean::cnstr_set(x_6, 0, x_20);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get(x_6, 0);
x_24 = lean::cnstr_get(x_6, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_6);
x_25 = lean::box(0);
lean::cnstr_set(x_4, 1, x_23);
lean::cnstr_set(x_4, 0, x_25);
x_26 = l_Lean_logElabException(x_1, x_22, x_4);
lean::dec(x_22);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_29 = x_26;
} else {
 lean::dec_ref(x_26);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_24);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_34 = x_26;
} else {
 lean::dec_ref(x_26);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_24);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 1);
x_38 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
lean::inc(x_38);
lean::dec(x_4);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 x_41 = x_37;
} else {
 lean::dec_ref(x_37);
 x_41 = lean::box(0);
}
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
x_44 = l_Lean_logElabException(x_1, x_38, x_43);
lean::dec(x_38);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_41;
}
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_40);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_52 = x_44;
} else {
 lean::dec_ref(x_44);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_41;
}
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_40);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
lean::dec(x_1);
x_55 = !lean::is_exclusive(x_4);
if (x_55 == 0)
{
return x_4;
}
else
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_4, 0);
x_57 = lean::cnstr_get(x_4, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_4);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
}
}
}
obj* l_Lean_processCommand(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_updateCmdPos___rarg(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_10 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_1);
lean::inc(x_10);
x_12 = l_Lean_Parser_parseCommand___main(x_10, x_1, x_8, x_11);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
lean::cnstr_set(x_7, 1, x_16);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::box(0);
lean::inc(x_17);
lean::cnstr_set(x_3, 1, x_17);
lean::cnstr_set(x_3, 0, x_18);
x_19 = l_Lean_Parser_isEOI(x_14);
if (x_19 == 0)
{
uint8 x_20; 
x_20 = l_Lean_Parser_isExitCommand(x_14);
if (x_20 == 0)
{
obj* x_21; 
lean::dec(x_17);
x_21 = l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(x_14, x_1, x_3);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
lean::dec(x_1);
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::dec(x_23);
x_24 = 0;
x_25 = lean::box(x_24);
lean::cnstr_set(x_21, 0, x_25);
return x_21;
}
else
{
obj* x_26; uint8 x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_27 = 0;
x_28 = lean::box(x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_21);
if (x_30 == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_21, 0);
lean::cnstr_set_tag(x_21, 0);
lean::cnstr_set(x_21, 0, x_18);
x_32 = l_Lean_runElab___at_Lean_processCommand___spec__1(x_31, x_1, x_21);
lean::dec(x_1);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_32);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_32, 0);
lean::dec(x_34);
x_35 = 0;
x_36 = lean::box(x_35);
lean::cnstr_set(x_32, 0, x_36);
return x_32;
}
else
{
obj* x_37; uint8 x_38; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::dec(x_32);
x_38 = 0;
x_39 = lean::box(x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
x_42 = lean::cnstr_get(x_32, 0);
x_43 = lean::cnstr_get(x_32, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_32);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_21, 0);
x_46 = lean::cnstr_get(x_21, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_21);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_18);
lean::cnstr_set(x_47, 1, x_46);
x_48 = l_Lean_runElab___at_Lean_processCommand___spec__1(x_45, x_1, x_47);
lean::dec(x_1);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; uint8 x_51; obj* x_52; obj* x_53; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_50 = x_48;
} else {
 lean::dec_ref(x_48);
 x_50 = lean::box(0);
}
x_51 = 0;
x_52 = lean::box(x_51);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_49);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_48, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_48, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_56 = x_48;
} else {
 lean::dec_ref(x_48);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
uint8 x_58; obj* x_59; obj* x_60; 
lean::dec(x_3);
lean::dec(x_14);
lean::dec(x_1);
x_58 = 1;
x_59 = lean::box(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_17);
return x_60;
}
}
else
{
uint8 x_61; obj* x_62; obj* x_63; 
lean::dec(x_3);
lean::dec(x_14);
lean::dec(x_1);
x_61 = 1;
x_62 = lean::box(x_61);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_17);
return x_63;
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; uint8 x_77; 
x_64 = lean::cnstr_get(x_7, 0);
x_65 = lean::cnstr_get(x_7, 1);
x_66 = lean::cnstr_get(x_7, 2);
x_67 = lean::cnstr_get(x_7, 3);
x_68 = lean::cnstr_get(x_7, 4);
lean::inc(x_68);
lean::inc(x_67);
lean::inc(x_66);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_64);
x_69 = l_Lean_Parser_parseCommand___main(x_64, x_1, x_8, x_65);
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
lean::dec(x_69);
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_74 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_74, 0, x_64);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set(x_74, 2, x_66);
lean::cnstr_set(x_74, 3, x_67);
lean::cnstr_set(x_74, 4, x_68);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_72);
x_76 = lean::box(0);
lean::inc(x_75);
lean::cnstr_set(x_3, 1, x_75);
lean::cnstr_set(x_3, 0, x_76);
x_77 = l_Lean_Parser_isEOI(x_71);
if (x_77 == 0)
{
uint8 x_78; 
x_78 = l_Lean_Parser_isExitCommand(x_71);
if (x_78 == 0)
{
obj* x_79; 
lean::dec(x_75);
x_79 = l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(x_71, x_1, x_3);
if (lean::obj_tag(x_79) == 0)
{
obj* x_80; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; 
lean::dec(x_1);
x_80 = lean::cnstr_get(x_79, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_81 = x_79;
} else {
 lean::dec_ref(x_79);
 x_81 = lean::box(0);
}
x_82 = 0;
x_83 = lean::box(x_82);
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_80);
return x_84;
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_79, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_79, 1);
lean::inc(x_86);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_87 = x_79;
} else {
 lean::dec_ref(x_79);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_87;
 lean::cnstr_set_tag(x_88, 0);
}
lean::cnstr_set(x_88, 0, x_76);
lean::cnstr_set(x_88, 1, x_86);
x_89 = l_Lean_runElab___at_Lean_processCommand___spec__1(x_85, x_1, x_88);
lean::dec(x_1);
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_91; uint8 x_92; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_91 = x_89;
} else {
 lean::dec_ref(x_89);
 x_91 = lean::box(0);
}
x_92 = 0;
x_93 = lean::box(x_92);
if (lean::is_scalar(x_91)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_91;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_95 = lean::cnstr_get(x_89, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_89, 1);
lean::inc(x_96);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_97 = x_89;
} else {
 lean::dec_ref(x_89);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8 x_99; obj* x_100; obj* x_101; 
lean::dec(x_3);
lean::dec(x_71);
lean::dec(x_1);
x_99 = 1;
x_100 = lean::box(x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_75);
return x_101;
}
}
else
{
uint8 x_102; obj* x_103; obj* x_104; 
lean::dec(x_3);
lean::dec(x_71);
lean::dec(x_1);
x_102 = 1;
x_103 = lean::box(x_102);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_75);
return x_104;
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; uint8 x_123; 
x_105 = lean::cnstr_get(x_3, 1);
lean::inc(x_105);
lean::dec(x_3);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_107 = lean::cnstr_get(x_105, 1);
lean::inc(x_107);
lean::dec(x_105);
x_108 = lean::cnstr_get(x_106, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_106, 2);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_106, 3);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_106, 4);
lean::inc(x_112);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 lean::cnstr_release(x_106, 2);
 lean::cnstr_release(x_106, 3);
 lean::cnstr_release(x_106, 4);
 x_113 = x_106;
} else {
 lean::dec_ref(x_106);
 x_113 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_108);
x_114 = l_Lean_Parser_parseCommand___main(x_108, x_1, x_107, x_109);
x_115 = lean::cnstr_get(x_114, 1);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_114, 0);
lean::inc(x_116);
lean::dec(x_114);
x_117 = lean::cnstr_get(x_115, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::is_scalar(x_113)) {
 x_119 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_119 = x_113;
}
lean::cnstr_set(x_119, 0, x_108);
lean::cnstr_set(x_119, 1, x_118);
lean::cnstr_set(x_119, 2, x_110);
lean::cnstr_set(x_119, 3, x_111);
lean::cnstr_set(x_119, 4, x_112);
x_120 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_117);
x_121 = lean::box(0);
lean::inc(x_120);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_120);
x_123 = l_Lean_Parser_isEOI(x_116);
if (x_123 == 0)
{
uint8 x_124; 
x_124 = l_Lean_Parser_isExitCommand(x_116);
if (x_124 == 0)
{
obj* x_125; 
lean::dec(x_120);
x_125 = l_Lean_runElab___at_Lean_elabCommandAtFrontend___spec__1(x_116, x_1, x_122);
if (lean::obj_tag(x_125) == 0)
{
obj* x_126; obj* x_127; uint8 x_128; obj* x_129; obj* x_130; 
lean::dec(x_1);
x_126 = lean::cnstr_get(x_125, 1);
lean::inc(x_126);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_127 = x_125;
} else {
 lean::dec_ref(x_125);
 x_127 = lean::box(0);
}
x_128 = 0;
x_129 = lean::box(x_128);
if (lean::is_scalar(x_127)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_127;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_126);
return x_130;
}
else
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
x_131 = lean::cnstr_get(x_125, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_125, 1);
lean::inc(x_132);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_133 = x_125;
} else {
 lean::dec_ref(x_125);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_133;
 lean::cnstr_set_tag(x_134, 0);
}
lean::cnstr_set(x_134, 0, x_121);
lean::cnstr_set(x_134, 1, x_132);
x_135 = l_Lean_runElab___at_Lean_processCommand___spec__1(x_131, x_1, x_134);
lean::dec(x_1);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_137; uint8 x_138; obj* x_139; obj* x_140; 
x_136 = lean::cnstr_get(x_135, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_137 = x_135;
} else {
 lean::dec_ref(x_135);
 x_137 = lean::box(0);
}
x_138 = 0;
x_139 = lean::box(x_138);
if (lean::is_scalar(x_137)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_137;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_136);
return x_140;
}
else
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_141 = lean::cnstr_get(x_135, 0);
lean::inc(x_141);
x_142 = lean::cnstr_get(x_135, 1);
lean::inc(x_142);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 x_143 = x_135;
} else {
 lean::dec_ref(x_135);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
lean::cnstr_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
uint8 x_145; obj* x_146; obj* x_147; 
lean::dec(x_122);
lean::dec(x_116);
lean::dec(x_1);
x_145 = 1;
x_146 = lean::box(x_145);
x_147 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_120);
return x_147;
}
}
else
{
uint8 x_148; obj* x_149; obj* x_150; 
lean::dec(x_122);
lean::dec(x_116);
lean::dec(x_1);
x_148 = 1;
x_149 = lean::box(x_148);
x_150 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_120);
return x_150;
}
}
}
else
{
uint8 x_151; 
lean::dec(x_1);
x_151 = !lean::is_exclusive(x_3);
if (x_151 == 0)
{
return x_3;
}
else
{
obj* x_152; obj* x_153; obj* x_154; 
x_152 = lean::cnstr_get(x_3, 0);
x_153 = lean::cnstr_get(x_3, 1);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_3);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_153);
return x_154;
}
}
}
}
obj* l_Lean_runElab___at_Lean_processCommand___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_runElab___at_Lean_processCommand___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_processCommandsAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = l_Lean_processCommand(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::unbox(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::cnstr_set(x_3, 0, x_8);
x_2 = x_3;
goto _start;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_2 = x_12;
goto _start;
}
}
else
{
uint8 x_14; 
lean::dec(x_1);
x_14 = !lean::is_exclusive(x_3);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_3, 0);
lean::dec(x_15);
x_16 = lean::box(0);
lean::cnstr_set(x_3, 0, x_16);
return x_3;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_3, 1);
lean::inc(x_17);
lean::dec(x_3);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8 x_20; 
lean::dec(x_1);
x_20 = !lean::is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_3, 0);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_3);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
}
obj* l_Lean_processCommandsAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_processCommandsAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_processCommandsAux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_processCommandsAux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_processCommandsAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_processCommandsAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_processCommandsAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_processCommandsAux___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_processCommandsAux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_processCommandsAux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_processCommands(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_processCommandsAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_absolutizeModuleName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid use of relative import, file name of main file is not available");
return x_1;
}
}
namespace lean {
obj* absolutize_module_name_core(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_5; 
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 0);
lean::dec(x_6);
lean::cnstr_set(x_4, 0, x_2);
return x_4;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_9; 
lean::dec(x_3);
lean::dec(x_2);
x_9 = !lean::is_exclusive(x_4);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_4, 0);
lean::dec(x_10);
x_11 = l_Lean_absolutizeModuleName___closed__1;
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_11);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
x_13 = l_Lean_absolutizeModuleName___closed__1;
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_17 = l_Lean_addRel___main(x_16, x_15);
lean::dec(x_15);
lean::dec(x_16);
x_18 = l___private_init_lean_path_1__pathSep___closed__1;
x_19 = lean::string_append(x_17, x_18);
x_20 = l_Lean_modNameToFileName___main(x_2);
lean::dec(x_2);
x_21 = lean::string_append(x_19, x_20);
lean::dec(x_20);
x_22 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
x_23 = lean::string_append(x_21, x_22);
x_24 = l_Lean_findOLean___closed__1;
x_25 = lean::string_append(x_23, x_24);
x_26 = lean::module_name_of_file_core(x_25, x_4);
return x_26;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_4);
x_9 = lean::nat_dec_lt(x_5, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_14 = lean::array_fget(x_4, x_5);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_5, x_15);
lean::dec(x_5);
x_17 = l_Lean_Syntax_asNode___main___rarg(x_14);
lean::dec(x_14);
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
lean::dec(x_17);
x_19 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_20 = lean::array_get(x_2, x_18, x_19);
x_21 = l_Lean_Syntax_isNone___rarg(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = l_Lean_Syntax_getNumArgs___rarg(x_20);
lean::dec(x_20);
x_23 = lean::nat_sub(x_22, x_15);
lean::dec(x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::inc(x_2);
x_25 = lean::array_get(x_2, x_18, x_15);
lean::dec(x_18);
x_26 = l_Lean_Syntax_getId___main___rarg(x_25);
lean::dec(x_25);
lean::inc(x_1);
x_27 = lean::absolutize_module_name_core(x_1, x_26, x_24, x_7);
if (lean::obj_tag(x_27) == 0)
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_6);
x_31 = lean::box(0);
lean::cnstr_set(x_27, 0, x_31);
x_5 = x_16;
x_6 = x_30;
x_7 = x_27;
goto _start;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_27, 0);
x_34 = lean::cnstr_get(x_27, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_27);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_6);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
x_5 = x_16;
x_6 = x_35;
x_7 = x_37;
goto _start;
}
}
else
{
uint8 x_39; 
lean::dec(x_16);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_39 = !lean::is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_27, 0);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_27);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_20);
x_43 = lean::box(0);
lean::inc(x_2);
x_44 = lean::array_get(x_2, x_18, x_15);
lean::dec(x_18);
x_45 = l_Lean_Syntax_getId___main___rarg(x_44);
lean::dec(x_44);
lean::inc(x_1);
x_46 = lean::absolutize_module_name_core(x_1, x_45, x_43, x_7);
if (lean::obj_tag(x_46) == 0)
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_46, 0);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_6);
x_50 = lean::box(0);
lean::cnstr_set(x_46, 0, x_50);
x_5 = x_16;
x_6 = x_49;
x_7 = x_46;
goto _start;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_46, 0);
x_53 = lean::cnstr_get(x_46, 1);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_46);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_6);
x_55 = lean::box(0);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
x_5 = x_16;
x_6 = x_54;
x_7 = x_56;
goto _start;
}
}
else
{
uint8 x_58; 
lean::dec(x_16);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_58 = !lean::is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = lean::cnstr_get(x_46, 0);
x_60 = lean::cnstr_get(x_46, 1);
lean::inc(x_60);
lean::inc(x_59);
lean::dec(x_46);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_4);
x_9 = lean::nat_dec_lt(x_5, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::array_fget(x_4, x_5);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_5, x_15);
lean::dec(x_5);
x_17 = l_Lean_Syntax_getArg___rarg(x_14, x_15);
x_18 = l_Lean_Syntax_getArgs___rarg(x_17);
lean::dec(x_17);
x_19 = lean::mk_nat_obj(0u);
lean::inc(x_3);
lean::inc(x_1);
x_20 = l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1(x_1, x_3, x_14, x_18, x_19, x_6, x_7);
lean::dec(x_18);
lean::dec(x_14);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::box(0);
lean::cnstr_set(x_20, 0, x_23);
x_5 = x_16;
x_6 = x_22;
x_7 = x_20;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
x_26 = lean::cnstr_get(x_20, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_20);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_5 = x_16;
x_6 = x_25;
x_7 = x_28;
goto _start;
}
}
else
{
uint8 x_30; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_1);
x_30 = !lean::is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_20, 0);
x_32 = lean::cnstr_get(x_20, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_20);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
obj* _init_l_Lean_processHeaderAux___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_mkInitAttr___closed__2;
x_2 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_processHeaderAux___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_processHeaderAux___closed__1;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_processHeaderAux(obj* x_1, obj* x_2, uint32 x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_5 = l_Lean_Syntax_asNode___main___rarg(x_2);
x_30 = lean::cnstr_get(x_5, 1);
lean::inc(x_30);
x_31 = lean::box(0);
x_32 = lean::mk_nat_obj(0u);
x_33 = lean::array_get(x_31, x_30, x_32);
lean::dec(x_30);
x_34 = l_Lean_Syntax_isNone___rarg(x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::box(0);
x_6 = x_35;
goto block_29;
}
else
{
obj* x_36; 
x_36 = l_Lean_processHeaderAux___closed__2;
x_6 = x_36;
goto block_29;
}
block_29:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::array_get(x_8, x_7, x_9);
x_11 = l_Lean_Syntax_getArgs___rarg(x_10);
lean::dec(x_10);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2(x_1, x_7, x_8, x_11, x_12, x_6, x_4);
lean::dec(x_11);
lean::dec(x_7);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::box(0);
lean::cnstr_set(x_13, 0, x_16);
x_17 = l_List_reverse___rarg(x_15);
x_18 = lean::import_modules_core(x_17, x_3, x_13);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_13);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
x_23 = l_List_reverse___rarg(x_19);
x_24 = lean::import_modules_core(x_23, x_3, x_22);
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_13, 0);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_13);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_3);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_processHeaderAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_4);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_processHeaderAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_6 = l_Lean_processHeaderAux(x_1, x_2, x_5, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_processHeader(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint32 x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_processHeaderAux(x_1, x_2, x_5, x_6);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
lean::cnstr_set(x_7, 0, x_10);
return x_7;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_3);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_7);
if (x_15 == 0)
{
obj* x_16; obj* x_17; uint32 x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_7, 0);
x_17 = lean::box(0);
lean::cnstr_set_tag(x_7, 0);
lean::cnstr_set(x_7, 0, x_17);
x_18 = 0;
x_19 = lean::mk_empty_environment_core(x_18, x_7);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = l_Lean_Syntax_getPos___rarg(x_2);
x_23 = lean::cnstr_get(x_4, 2);
x_24 = lean::cnstr_get(x_4, 1);
x_25 = lean::box(0);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::mk_nat_obj(0u);
x_27 = l_Lean_FileMap_toPosition___main(x_23, x_26);
x_28 = 2;
x_29 = l_String_splitAux___main___closed__1;
lean::inc(x_24);
x_30 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_30, 0, x_24);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_25);
lean::cnstr_set(x_30, 3, x_29);
lean::cnstr_set(x_30, 4, x_16);
lean::cnstr_set_scalar(x_30, sizeof(void*)*5, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_21);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set(x_19, 0, x_32);
return x_19;
}
else
{
obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_22, 0);
lean::inc(x_33);
lean::dec(x_22);
x_34 = l_Lean_FileMap_toPosition___main(x_23, x_33);
lean::dec(x_33);
x_35 = 2;
x_36 = l_String_splitAux___main___closed__1;
lean::inc(x_24);
x_37 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_37, 0, x_24);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set(x_37, 2, x_25);
lean::cnstr_set(x_37, 3, x_36);
lean::cnstr_set(x_37, 4, x_16);
lean::cnstr_set_scalar(x_37, sizeof(void*)*5, x_35);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_3);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_21);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set(x_19, 0, x_39);
return x_19;
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_19, 0);
x_41 = lean::cnstr_get(x_19, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_19);
x_42 = l_Lean_Syntax_getPos___rarg(x_2);
x_43 = lean::cnstr_get(x_4, 2);
x_44 = lean::cnstr_get(x_4, 1);
x_45 = lean::box(0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_46 = lean::mk_nat_obj(0u);
x_47 = l_Lean_FileMap_toPosition___main(x_43, x_46);
x_48 = 2;
x_49 = l_String_splitAux___main___closed__1;
lean::inc(x_44);
x_50 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_47);
lean::cnstr_set(x_50, 2, x_45);
lean::cnstr_set(x_50, 3, x_49);
lean::cnstr_set(x_50, 4, x_16);
lean::cnstr_set_scalar(x_50, sizeof(void*)*5, x_48);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_3);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_40);
lean::cnstr_set(x_52, 1, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_41);
return x_53;
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_42, 0);
lean::inc(x_54);
lean::dec(x_42);
x_55 = l_Lean_FileMap_toPosition___main(x_43, x_54);
lean::dec(x_54);
x_56 = 2;
x_57 = l_String_splitAux___main___closed__1;
lean::inc(x_44);
x_58 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_58, 0, x_44);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set(x_58, 2, x_45);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set(x_58, 4, x_16);
lean::cnstr_set_scalar(x_58, sizeof(void*)*5, x_56);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_3);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_40);
lean::cnstr_set(x_60, 1, x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_41);
return x_61;
}
}
}
else
{
uint8 x_62; 
lean::dec(x_16);
lean::dec(x_3);
x_62 = !lean::is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_19, 0);
x_64 = lean::cnstr_get(x_19, 1);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_19);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint32 x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_7, 0);
x_67 = lean::cnstr_get(x_7, 1);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_7);
x_68 = lean::box(0);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_67);
x_70 = 0;
x_71 = lean::mk_empty_environment_core(x_70, x_69);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_71, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_74 = x_71;
} else {
 lean::dec_ref(x_71);
 x_74 = lean::box(0);
}
x_75 = l_Lean_Syntax_getPos___rarg(x_2);
x_76 = lean::cnstr_get(x_4, 2);
x_77 = lean::cnstr_get(x_4, 1);
x_78 = lean::box(0);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_79 = lean::mk_nat_obj(0u);
x_80 = l_Lean_FileMap_toPosition___main(x_76, x_79);
x_81 = 2;
x_82 = l_String_splitAux___main___closed__1;
lean::inc(x_77);
x_83 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_83, 0, x_77);
lean::cnstr_set(x_83, 1, x_80);
lean::cnstr_set(x_83, 2, x_78);
lean::cnstr_set(x_83, 3, x_82);
lean::cnstr_set(x_83, 4, x_66);
lean::cnstr_set_scalar(x_83, sizeof(void*)*5, x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_3);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_72);
lean::cnstr_set(x_85, 1, x_84);
if (lean::is_scalar(x_74)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_74;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_73);
return x_86;
}
else
{
obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_87 = lean::cnstr_get(x_75, 0);
lean::inc(x_87);
lean::dec(x_75);
x_88 = l_Lean_FileMap_toPosition___main(x_76, x_87);
lean::dec(x_87);
x_89 = 2;
x_90 = l_String_splitAux___main___closed__1;
lean::inc(x_77);
x_91 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_91, 0, x_77);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_78);
lean::cnstr_set(x_91, 3, x_90);
lean::cnstr_set(x_91, 4, x_66);
lean::cnstr_set_scalar(x_91, sizeof(void*)*5, x_89);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_3);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_72);
lean::cnstr_set(x_93, 1, x_92);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_73);
return x_94;
}
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_66);
lean::dec(x_3);
x_95 = lean::cnstr_get(x_71, 0);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_71, 1);
lean::inc(x_96);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_97 = x_71;
} else {
 lean::dec_ref(x_71);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
obj* l_Lean_processHeader___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint32 x_7; obj* x_8; 
x_7 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_8 = l_Lean_processHeader(x_1, x_2, x_3, x_4, x_7, x_6);
lean::dec(x_4);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_toBaseDir(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean_io_realpath(x_8, x_2);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_System_FilePath_dirName(x_11);
lean::cnstr_set(x_1, 0, x_12);
lean::cnstr_set(x_9, 0, x_1);
return x_9;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_9);
x_15 = l_System_FilePath_dirName(x_13);
lean::cnstr_set(x_1, 0, x_15);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8 x_17; 
lean::free_heap_obj(x_1);
x_17 = !lean::is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_9, 0);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_9);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_1, 0);
lean::inc(x_21);
lean::dec(x_1);
x_22 = lean_io_realpath(x_21, x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_25 = x_22;
} else {
 lean::dec_ref(x_22);
 x_25 = lean::box(0);
}
x_26 = l_System_FilePath_dirName(x_23);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_22, 1);
lean::inc(x_30);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_31 = x_22;
} else {
 lean::dec_ref(x_22);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
obj* _init_l_Lean_testFrontend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("root");
return x_1;
}
}
obj* _init_l_Lean_testFrontend___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_Lean_testFrontend___closed__1;
x_3 = lean::box(0);
x_4 = l_Lean_Options_empty;
x_5 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set(x_5, 4, x_1);
lean::cnstr_set(x_5, 5, x_1);
return x_5;
}
}
obj* _init_l_Lean_testFrontend___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_testFrontend___closed__2;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _init_l_Lean_testFrontend___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("<input>");
return x_1;
}
}
obj* l_Lean_testFrontend(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::mk_empty_environment_core(x_4, x_3);
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
lean::inc(x_2);
x_9 = l_Lean_toBaseDir(x_2, x_5);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::cnstr_set(x_9, 0, x_8);
if (lean::obj_tag(x_2) == 0)
{
obj* x_108; 
x_108 = l_Lean_testFrontend___closed__4;
x_12 = x_108;
goto block_107;
}
else
{
obj* x_109; 
x_109 = lean::cnstr_get(x_2, 0);
lean::inc(x_109);
lean::dec(x_2);
x_12 = x_109;
goto block_107;
}
block_107:
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_Lean_Parser_mkParserContextCore(x_7, x_1, x_12);
lean::inc(x_13);
x_14 = l_Lean_Parser_parseHeader(x_7, x_13);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_19 = l_Lean_processHeader(x_11, x_16, x_18, x_13, x_4, x_9);
lean::dec(x_16);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_23 = lean::cnstr_get(x_19, 1);
x_24 = lean::cnstr_get(x_21, 0);
x_25 = lean::cnstr_get(x_21, 1);
x_26 = lean::mk_nat_obj(0u);
x_27 = l_Lean_NameGenerator_Inhabited___closed__3;
x_28 = l_Lean_testFrontend___closed__3;
x_29 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_26);
lean::cnstr_set(x_29, 3, x_27);
lean::cnstr_set(x_29, 4, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_17);
lean::cnstr_set(x_19, 1, x_30);
lean::cnstr_set(x_19, 0, x_8);
x_31 = l_Lean_processCommandsAux___main___rarg(x_13, x_19);
if (lean::obj_tag(x_31) == 0)
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_31, 1);
x_34 = lean::cnstr_get(x_31, 0);
lean::dec(x_34);
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
lean::dec(x_33);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
lean::dec(x_35);
lean::cnstr_set(x_21, 1, x_37);
lean::cnstr_set(x_21, 0, x_36);
lean::cnstr_set(x_31, 1, x_23);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_31, 1);
lean::inc(x_38);
lean::dec(x_31);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_39, 1);
lean::inc(x_41);
lean::dec(x_39);
lean::cnstr_set(x_21, 1, x_41);
lean::cnstr_set(x_21, 0, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_21);
lean::cnstr_set(x_42, 1, x_23);
return x_42;
}
}
else
{
uint8 x_43; 
x_43 = !lean::is_exclusive(x_31);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_31, 1);
x_45 = lean::cnstr_get(x_31, 0);
lean::dec(x_45);
x_46 = lean::cnstr_get(x_44, 0);
lean::inc(x_46);
lean::dec(x_44);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
lean::dec(x_46);
lean::cnstr_set(x_21, 1, x_48);
lean::cnstr_set(x_21, 0, x_47);
lean::cnstr_set_tag(x_31, 0);
lean::cnstr_set(x_31, 1, x_23);
lean::cnstr_set(x_31, 0, x_21);
return x_31;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_49 = lean::cnstr_get(x_31, 1);
lean::inc(x_49);
lean::dec(x_31);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
lean::dec(x_49);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_50, 1);
lean::inc(x_52);
lean::dec(x_50);
lean::cnstr_set(x_21, 1, x_52);
lean::cnstr_set(x_21, 0, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_21);
lean::cnstr_set(x_53, 1, x_23);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_54 = lean::cnstr_get(x_19, 1);
x_55 = lean::cnstr_get(x_21, 0);
x_56 = lean::cnstr_get(x_21, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_21);
x_57 = lean::mk_nat_obj(0u);
x_58 = l_Lean_NameGenerator_Inhabited___closed__3;
x_59 = l_Lean_testFrontend___closed__3;
x_60 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_60, 0, x_55);
lean::cnstr_set(x_60, 1, x_56);
lean::cnstr_set(x_60, 2, x_57);
lean::cnstr_set(x_60, 3, x_58);
lean::cnstr_set(x_60, 4, x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_17);
lean::cnstr_set(x_19, 1, x_61);
lean::cnstr_set(x_19, 0, x_8);
x_62 = l_Lean_processCommandsAux___main___rarg(x_13, x_19);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_64 = x_62;
} else {
 lean::dec_ref(x_62);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
lean::dec(x_63);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_65, 1);
lean::inc(x_67);
lean::dec(x_65);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_67);
if (lean::is_scalar(x_64)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_64;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_54);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_70 = lean::cnstr_get(x_62, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_71 = x_62;
} else {
 lean::dec_ref(x_62);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
lean::dec(x_70);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
lean::dec(x_72);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_74);
if (lean::is_scalar(x_71)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_71;
 lean::cnstr_set_tag(x_76, 0);
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_54);
return x_76;
}
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_77 = lean::cnstr_get(x_19, 0);
x_78 = lean::cnstr_get(x_19, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_19);
x_79 = lean::cnstr_get(x_77, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_81 = x_77;
} else {
 lean::dec_ref(x_77);
 x_81 = lean::box(0);
}
x_82 = lean::mk_nat_obj(0u);
x_83 = l_Lean_NameGenerator_Inhabited___closed__3;
x_84 = l_Lean_testFrontend___closed__3;
x_85 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_85, 0, x_79);
lean::cnstr_set(x_85, 1, x_80);
lean::cnstr_set(x_85, 2, x_82);
lean::cnstr_set(x_85, 3, x_83);
lean::cnstr_set(x_85, 4, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_17);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_8);
lean::cnstr_set(x_87, 1, x_86);
x_88 = l_Lean_processCommandsAux___main___rarg(x_13, x_87);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 x_90 = x_88;
} else {
 lean::dec_ref(x_88);
 x_90 = lean::box(0);
}
x_91 = lean::cnstr_get(x_89, 0);
lean::inc(x_91);
lean::dec(x_89);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
lean::dec(x_91);
if (lean::is_scalar(x_81)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_81;
}
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
if (lean::is_scalar(x_90)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_90;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_78);
return x_95;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_96 = lean::cnstr_get(x_88, 1);
lean::inc(x_96);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 x_97 = x_88;
} else {
 lean::dec_ref(x_88);
 x_97 = lean::box(0);
}
x_98 = lean::cnstr_get(x_96, 0);
lean::inc(x_98);
lean::dec(x_96);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_98, 1);
lean::inc(x_100);
lean::dec(x_98);
if (lean::is_scalar(x_81)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_81;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_100);
if (lean::is_scalar(x_97)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_97;
 lean::cnstr_set_tag(x_102, 0);
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_78);
return x_102;
}
}
}
else
{
uint8 x_103; 
lean::dec(x_17);
lean::dec(x_13);
x_103 = !lean::is_exclusive(x_19);
if (x_103 == 0)
{
return x_19;
}
else
{
obj* x_104; obj* x_105; obj* x_106; 
x_104 = lean::cnstr_get(x_19, 0);
x_105 = lean::cnstr_get(x_19, 1);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_19);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_110 = lean::cnstr_get(x_9, 0);
x_111 = lean::cnstr_get(x_9, 1);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_9);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_8);
lean::cnstr_set(x_112, 1, x_111);
if (lean::obj_tag(x_2) == 0)
{
obj* x_153; 
x_153 = l_Lean_testFrontend___closed__4;
x_113 = x_153;
goto block_152;
}
else
{
obj* x_154; 
x_154 = lean::cnstr_get(x_2, 0);
lean::inc(x_154);
lean::dec(x_2);
x_113 = x_154;
goto block_152;
}
block_152:
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_114 = l_Lean_Parser_mkParserContextCore(x_7, x_1, x_113);
lean::inc(x_114);
x_115 = l_Lean_Parser_parseHeader(x_7, x_114);
x_116 = lean::cnstr_get(x_115, 1);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_115, 0);
lean::inc(x_117);
lean::dec(x_115);
x_118 = lean::cnstr_get(x_116, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_116, 1);
lean::inc(x_119);
lean::dec(x_116);
x_120 = l_Lean_processHeader(x_110, x_117, x_119, x_114, x_4, x_112);
lean::dec(x_117);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_120, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_123 = x_120;
} else {
 lean::dec_ref(x_120);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_121, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_121, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 x_126 = x_121;
} else {
 lean::dec_ref(x_121);
 x_126 = lean::box(0);
}
x_127 = lean::mk_nat_obj(0u);
x_128 = l_Lean_NameGenerator_Inhabited___closed__3;
x_129 = l_Lean_testFrontend___closed__3;
x_130 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_130, 0, x_124);
lean::cnstr_set(x_130, 1, x_125);
lean::cnstr_set(x_130, 2, x_127);
lean::cnstr_set(x_130, 3, x_128);
lean::cnstr_set(x_130, 4, x_129);
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_118);
if (lean::is_scalar(x_123)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_123;
}
lean::cnstr_set(x_132, 0, x_8);
lean::cnstr_set(x_132, 1, x_131);
x_133 = l_Lean_processCommandsAux___main___rarg(x_114, x_132);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_134 = lean::cnstr_get(x_133, 1);
lean::inc(x_134);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_135 = x_133;
} else {
 lean::dec_ref(x_133);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_134, 0);
lean::inc(x_136);
lean::dec(x_134);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
x_138 = lean::cnstr_get(x_136, 1);
lean::inc(x_138);
lean::dec(x_136);
if (lean::is_scalar(x_126)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_126;
}
lean::cnstr_set(x_139, 0, x_137);
lean::cnstr_set(x_139, 1, x_138);
if (lean::is_scalar(x_135)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_135;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_122);
return x_140;
}
else
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_141 = lean::cnstr_get(x_133, 1);
lean::inc(x_141);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_142 = x_133;
} else {
 lean::dec_ref(x_133);
 x_142 = lean::box(0);
}
x_143 = lean::cnstr_get(x_141, 0);
lean::inc(x_143);
lean::dec(x_141);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_143, 1);
lean::inc(x_145);
lean::dec(x_143);
if (lean::is_scalar(x_126)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_126;
}
lean::cnstr_set(x_146, 0, x_144);
lean::cnstr_set(x_146, 1, x_145);
if (lean::is_scalar(x_142)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_142;
 lean::cnstr_set_tag(x_147, 0);
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_122);
return x_147;
}
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_118);
lean::dec(x_114);
x_148 = lean::cnstr_get(x_120, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_120, 1);
lean::inc(x_149);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_150 = x_120;
} else {
 lean::dec_ref(x_120);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set(x_151, 1, x_149);
return x_151;
}
}
}
}
else
{
uint8 x_155; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_155 = !lean::is_exclusive(x_9);
if (x_155 == 0)
{
return x_9;
}
else
{
obj* x_156; obj* x_157; obj* x_158; 
x_156 = lean::cnstr_get(x_9, 0);
x_157 = lean::cnstr_get(x_9, 1);
lean::inc(x_157);
lean::inc(x_156);
lean::dec(x_9);
x_158 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_158, 0, x_156);
lean::cnstr_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_159 = lean::cnstr_get(x_5, 0);
x_160 = lean::cnstr_get(x_5, 1);
lean::inc(x_160);
lean::inc(x_159);
lean::dec(x_5);
x_161 = lean::box(0);
x_162 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_160);
lean::inc(x_2);
x_163 = l_Lean_toBaseDir(x_2, x_162);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 x_166 = x_163;
} else {
 lean::dec_ref(x_163);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_161);
lean::cnstr_set(x_167, 1, x_165);
if (lean::obj_tag(x_2) == 0)
{
obj* x_208; 
x_208 = l_Lean_testFrontend___closed__4;
x_168 = x_208;
goto block_207;
}
else
{
obj* x_209; 
x_209 = lean::cnstr_get(x_2, 0);
lean::inc(x_209);
lean::dec(x_2);
x_168 = x_209;
goto block_207;
}
block_207:
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_169 = l_Lean_Parser_mkParserContextCore(x_159, x_1, x_168);
lean::inc(x_169);
x_170 = l_Lean_Parser_parseHeader(x_159, x_169);
x_171 = lean::cnstr_get(x_170, 1);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_170, 0);
lean::inc(x_172);
lean::dec(x_170);
x_173 = lean::cnstr_get(x_171, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
lean::dec(x_171);
x_175 = l_Lean_processHeader(x_164, x_172, x_174, x_169, x_4, x_167);
lean::dec(x_172);
if (lean::obj_tag(x_175) == 0)
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_175, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 x_178 = x_175;
} else {
 lean::dec_ref(x_175);
 x_178 = lean::box(0);
}
x_179 = lean::cnstr_get(x_176, 0);
lean::inc(x_179);
x_180 = lean::cnstr_get(x_176, 1);
lean::inc(x_180);
if (lean::is_exclusive(x_176)) {
 lean::cnstr_release(x_176, 0);
 lean::cnstr_release(x_176, 1);
 x_181 = x_176;
} else {
 lean::dec_ref(x_176);
 x_181 = lean::box(0);
}
x_182 = lean::mk_nat_obj(0u);
x_183 = l_Lean_NameGenerator_Inhabited___closed__3;
x_184 = l_Lean_testFrontend___closed__3;
x_185 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_185, 0, x_179);
lean::cnstr_set(x_185, 1, x_180);
lean::cnstr_set(x_185, 2, x_182);
lean::cnstr_set(x_185, 3, x_183);
lean::cnstr_set(x_185, 4, x_184);
x_186 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_173);
if (lean::is_scalar(x_178)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_178;
}
lean::cnstr_set(x_187, 0, x_161);
lean::cnstr_set(x_187, 1, x_186);
x_188 = l_Lean_processCommandsAux___main___rarg(x_169, x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
x_189 = lean::cnstr_get(x_188, 1);
lean::inc(x_189);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_190 = x_188;
} else {
 lean::dec_ref(x_188);
 x_190 = lean::box(0);
}
x_191 = lean::cnstr_get(x_189, 0);
lean::inc(x_191);
lean::dec(x_189);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
x_193 = lean::cnstr_get(x_191, 1);
lean::inc(x_193);
lean::dec(x_191);
if (lean::is_scalar(x_181)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_181;
}
lean::cnstr_set(x_194, 0, x_192);
lean::cnstr_set(x_194, 1, x_193);
if (lean::is_scalar(x_190)) {
 x_195 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_195 = x_190;
}
lean::cnstr_set(x_195, 0, x_194);
lean::cnstr_set(x_195, 1, x_177);
return x_195;
}
else
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
x_196 = lean::cnstr_get(x_188, 1);
lean::inc(x_196);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 x_197 = x_188;
} else {
 lean::dec_ref(x_188);
 x_197 = lean::box(0);
}
x_198 = lean::cnstr_get(x_196, 0);
lean::inc(x_198);
lean::dec(x_196);
x_199 = lean::cnstr_get(x_198, 0);
lean::inc(x_199);
x_200 = lean::cnstr_get(x_198, 1);
lean::inc(x_200);
lean::dec(x_198);
if (lean::is_scalar(x_181)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_181;
}
lean::cnstr_set(x_201, 0, x_199);
lean::cnstr_set(x_201, 1, x_200);
if (lean::is_scalar(x_197)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_197;
 lean::cnstr_set_tag(x_202, 0);
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_177);
return x_202;
}
}
else
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
lean::dec(x_173);
lean::dec(x_169);
x_203 = lean::cnstr_get(x_175, 0);
lean::inc(x_203);
x_204 = lean::cnstr_get(x_175, 1);
lean::inc(x_204);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 x_205 = x_175;
} else {
 lean::dec_ref(x_175);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_203);
lean::cnstr_set(x_206, 1, x_204);
return x_206;
}
}
}
else
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
lean::dec(x_159);
lean::dec(x_2);
lean::dec(x_1);
x_210 = lean::cnstr_get(x_163, 0);
lean::inc(x_210);
x_211 = lean::cnstr_get(x_163, 1);
lean::inc(x_211);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 x_212 = x_163;
} else {
 lean::dec_ref(x_163);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
lean::cnstr_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
uint8 x_214; 
lean::dec(x_2);
lean::dec(x_1);
x_214 = !lean::is_exclusive(x_5);
if (x_214 == 0)
{
return x_5;
}
else
{
obj* x_215; obj* x_216; obj* x_217; 
x_215 = lean::cnstr_get(x_5, 0);
x_216 = lean::cnstr_get(x_5, 1);
lean::inc(x_216);
lean::inc(x_215);
lean::dec(x_5);
x_217 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_217, 0, x_215);
lean::cnstr_set(x_217, 1, x_216);
return x_217;
}
}
}
}
obj* l_Lean_Elab_Inhabited___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_ElabException_Inhabited___closed__2;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_ElabException_Inhabited___closed__2;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_Inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_Inhabited___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_Inhabited___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_Inhabited(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_head___main___at_Lean_Elab_getScope___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_ElabScope_Inhabited___closed__1;
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Lean_Elab_getScope___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 0);
lean::dec(x_4);
x_5 = lean::cnstr_get(x_3, 4);
lean::inc(x_5);
x_6 = l_List_head___main___at_Lean_Elab_getScope___spec__1(x_5);
lean::dec(x_5);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 4);
lean::inc(x_8);
x_9 = l_List_head___main___at_Lean_Elab_getScope___spec__1(x_8);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
}
}
obj* l_Lean_Elab_getScope(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_getScope___rarg), 1, 0);
return x_2;
}
}
obj* l_List_head___main___at_Lean_Elab_getScope___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_head___main___at_Lean_Elab_getScope___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elab_getScope___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getScope(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elab_getOpenDecls___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getScope___rarg(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_4, 4);
lean::inc(x_5);
lean::dec(x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_6, 4);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_2);
if (x_10 == 0)
{
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_Lean_Elab_getOpenDecls(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_getOpenDecls___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Elab_getOpenDecls___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getOpenDecls(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elab_getUniverses___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getScope___rarg(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_4, 5);
lean::inc(x_5);
lean::dec(x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_6, 5);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_2);
if (x_10 == 0)
{
return x_2;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_Lean_Elab_getUniverses(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_getUniverses___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Elab_getUniverses___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getUniverses(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Elab_getNamespace___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 0);
lean::dec(x_4);
x_5 = lean::cnstr_get(x_3, 4);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = lean::box(0);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
lean::dec(x_7);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 4);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_9);
return x_15;
}
}
}
}
obj* l_Lean_Elab_getNamespace(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_getNamespace___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Elab_getNamespace___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_getNamespace(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_rootNamespace___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("_root_");
return x_1;
}
}
obj* _init_l_Lean_Elab_rootNamespace___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Elab_rootNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Elab_rootNamespace() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Elab_rootNamespace___closed__2;
return x_1;
}
}
obj* l_Lean_Elab_removeRoot(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Elab_rootNamespace;
x_3 = lean::box(0);
x_4 = l_Lean_Name_replacePrefix___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingScopes___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_2);
x_8 = l_Lean_Name_append___main(x_7, x_2);
x_9 = l_Lean_isNamespace(x_1, x_8);
if (x_9 == 0)
{
lean::dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
obj* x_11; 
lean::dec(x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
}
obj* l_Lean_Elab_resolveNamespaceUsingScopes___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScopes___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingScopes(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScopes___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingScopes___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScopes(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_2);
x_8 = l_Lean_Name_append___main(x_7, x_2);
x_9 = l_Lean_isNamespace(x_1, x_8);
if (x_9 == 0)
{
lean::dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
obj* x_11; 
lean::dec(x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_3, 1);
x_3 = x_12;
goto _start;
}
}
}
}
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elab_resolveNamespaceUsingOpenDecls___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Elab_resolveNamespace___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown namespace '");
return x_1;
}
}
obj* l_Lean_Elab_resolveNamespace(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::box(0);
lean::inc(x_5);
lean::cnstr_set(x_3, 0, x_7);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_9 = l_Lean_isNamespace(x_8, x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_5, 4);
lean::inc(x_10);
lean::inc(x_1);
x_11 = l_Lean_Elab_resolveNamespaceUsingScopes___main(x_8, x_1, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; 
lean::dec(x_5);
x_12 = l_Lean_Elab_getOpenDecls___rarg(x_3);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_1);
x_15 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_8, x_1, x_14);
lean::dec(x_14);
lean::dec(x_8);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = l_System_FilePath_dirName___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_1);
x_18 = l_Lean_Elab_resolveNamespace___closed__1;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean::string_append(x_19, x_20);
x_22 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set_tag(x_12, 1);
lean::cnstr_set(x_12, 0, x_22);
return x_12;
}
else
{
obj* x_23; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
lean::dec(x_15);
lean::cnstr_set(x_12, 0, x_23);
return x_12;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_12, 0);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_12);
lean::inc(x_1);
x_26 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_8, x_1, x_24);
lean::dec(x_24);
lean::dec(x_8);
if (lean::obj_tag(x_26) == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_Elab_resolveNamespace___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_31 = l_Char_HasRepr___closed__1;
x_32 = lean::string_append(x_30, x_31);
x_33 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_1);
x_35 = lean::cnstr_get(x_26, 0);
lean::inc(x_35);
lean::dec(x_26);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_25);
return x_36;
}
}
}
else
{
uint8 x_37; 
lean::dec(x_8);
lean::dec(x_1);
x_37 = !lean::is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_12, 0);
x_39 = lean::cnstr_get(x_12, 1);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_12);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
obj* x_41; obj* x_42; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_1);
x_41 = lean::cnstr_get(x_11, 0);
lean::inc(x_41);
lean::dec(x_11);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
return x_42;
}
}
else
{
obj* x_43; 
lean::dec(x_8);
lean::dec(x_3);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_1);
lean::cnstr_set(x_43, 1, x_5);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_3, 1);
lean::inc(x_44);
lean::dec(x_3);
x_45 = lean::box(0);
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_48 = l_Lean_isNamespace(x_47, x_1);
if (x_48 == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::cnstr_get(x_44, 4);
lean::inc(x_49);
lean::inc(x_1);
x_50 = l_Lean_Elab_resolveNamespaceUsingScopes___main(x_47, x_1, x_49);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; 
lean::dec(x_44);
x_51 = l_Lean_Elab_getOpenDecls___rarg(x_46);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_54 = x_51;
} else {
 lean::dec_ref(x_51);
 x_54 = lean::box(0);
}
lean::inc(x_1);
x_55 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_47, x_1, x_52);
lean::dec(x_52);
lean::dec(x_47);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_56 = l_System_FilePath_dirName___closed__1;
x_57 = l_Lean_Name_toStringWithSep___main(x_56, x_1);
x_58 = l_Lean_Elab_resolveNamespace___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_60 = l_Char_HasRepr___closed__1;
x_61 = lean::string_append(x_59, x_60);
x_62 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
if (lean::is_scalar(x_54)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_54;
 lean::cnstr_set_tag(x_63, 1);
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_53);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_1);
x_64 = lean::cnstr_get(x_55, 0);
lean::inc(x_64);
lean::dec(x_55);
if (lean::is_scalar(x_54)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_54;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_53);
return x_65;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_47);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_51, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_51, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_68 = x_51;
} else {
 lean::dec_ref(x_51);
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
obj* x_70; obj* x_71; 
lean::dec(x_47);
lean::dec(x_46);
lean::dec(x_1);
x_70 = lean::cnstr_get(x_50, 0);
lean::inc(x_70);
lean::dec(x_50);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_44);
return x_71;
}
}
else
{
obj* x_72; 
lean::dec(x_47);
lean::dec(x_46);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_1);
lean::cnstr_set(x_72, 1, x_44);
return x_72;
}
}
}
}
obj* l_Lean_Elab_resolveNamespace___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_resolveNamespace(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_runIOUnsafe___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
x_5 = lean::apply_1(x_1, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = !lean::is_exclusive(x_3);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_3, 0);
lean::dec(x_8);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_3, 0);
lean::dec(x_13);
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_14);
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
return x_17;
}
}
}
}
obj* l_Lean_Elab_runIOUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_runIOUnsafe___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Elab_runIOUnsafe___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_runIOUnsafe___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_runIO___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_ElabException_Inhabited___closed__2;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_ElabException_Inhabited___closed__2;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_runIO(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_runIO___rarg), 1, 0);
return x_4;
}
}
obj* l_Lean_Elab_runIO___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_runIO(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_namegenerator(obj*);
obj* initialize_init_lean_scopes(obj*);
obj* initialize_init_lean_parser_module(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_namegenerator(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_scopes(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
l_Lean_OpenDecl_Inhabited___closed__1 = _init_l_Lean_OpenDecl_Inhabited___closed__1();
lean::mark_persistent(l_Lean_OpenDecl_Inhabited___closed__1);
l_Lean_OpenDecl_Inhabited = _init_l_Lean_OpenDecl_Inhabited();
lean::mark_persistent(l_Lean_OpenDecl_Inhabited);
l_Lean_OpenDecl_HasToString___closed__1 = _init_l_Lean_OpenDecl_HasToString___closed__1();
lean::mark_persistent(l_Lean_OpenDecl_HasToString___closed__1);
l_Lean_ElabScope_Inhabited___closed__1 = _init_l_Lean_ElabScope_Inhabited___closed__1();
lean::mark_persistent(l_Lean_ElabScope_Inhabited___closed__1);
l_Lean_ElabScope_Inhabited = _init_l_Lean_ElabScope_Inhabited();
lean::mark_persistent(l_Lean_ElabScope_Inhabited);
l_Lean_ElabException_Inhabited___closed__1 = _init_l_Lean_ElabException_Inhabited___closed__1();
lean::mark_persistent(l_Lean_ElabException_Inhabited___closed__1);
l_Lean_ElabException_Inhabited___closed__2 = _init_l_Lean_ElabException_Inhabited___closed__2();
lean::mark_persistent(l_Lean_ElabException_Inhabited___closed__2);
l_Lean_ElabException_Inhabited = _init_l_Lean_ElabException_Inhabited();
lean::mark_persistent(l_Lean_ElabException_Inhabited);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1);
w = l_Lean_mkBuiltinTermElabTable(w);
if (io_result_is_error(w)) return w;
l_Lean_builtinTermElabTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_builtinTermElabTable);
w = l_Lean_mkBuiltinCommandElabTable(w);
if (io_result_is_error(w)) return w;
l_Lean_builtinCommandElabTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_builtinCommandElabTable);
l_Lean_addBuiltinTermElab___closed__1 = _init_l_Lean_addBuiltinTermElab___closed__1();
lean::mark_persistent(l_Lean_addBuiltinTermElab___closed__1);
l_Lean_addBuiltinTermElab___closed__2 = _init_l_Lean_addBuiltinTermElab___closed__2();
lean::mark_persistent(l_Lean_addBuiltinTermElab___closed__2);
l_Lean_addBuiltinCommandElab___closed__1 = _init_l_Lean_addBuiltinCommandElab___closed__1();
lean::mark_persistent(l_Lean_addBuiltinCommandElab___closed__1);
l_Lean_checkSyntaxNodeKind___closed__1 = _init_l_Lean_checkSyntaxNodeKind___closed__1();
lean::mark_persistent(l_Lean_checkSyntaxNodeKind___closed__1);
l_Lean_syntaxNodeKindOfAttrParam___closed__1 = _init_l_Lean_syntaxNodeKindOfAttrParam___closed__1();
lean::mark_persistent(l_Lean_syntaxNodeKindOfAttrParam___closed__1);
l_Lean_syntaxNodeKindOfAttrParam___closed__2 = _init_l_Lean_syntaxNodeKindOfAttrParam___closed__2();
lean::mark_persistent(l_Lean_syntaxNodeKindOfAttrParam___closed__2);
l_Lean_declareBuiltinElab___closed__1 = _init_l_Lean_declareBuiltinElab___closed__1();
lean::mark_persistent(l_Lean_declareBuiltinElab___closed__1);
l_Lean_declareBuiltinElab___closed__2 = _init_l_Lean_declareBuiltinElab___closed__2();
lean::mark_persistent(l_Lean_declareBuiltinElab___closed__2);
l_Lean_declareBuiltinElab___closed__3 = _init_l_Lean_declareBuiltinElab___closed__3();
lean::mark_persistent(l_Lean_declareBuiltinElab___closed__3);
l_Lean_declareBuiltinTermElab___closed__1 = _init_l_Lean_declareBuiltinTermElab___closed__1();
lean::mark_persistent(l_Lean_declareBuiltinTermElab___closed__1);
l_Lean_declareBuiltinTermElab___closed__2 = _init_l_Lean_declareBuiltinTermElab___closed__2();
lean::mark_persistent(l_Lean_declareBuiltinTermElab___closed__2);
l_Lean_declareBuiltinCommandElab___closed__1 = _init_l_Lean_declareBuiltinCommandElab___closed__1();
lean::mark_persistent(l_Lean_declareBuiltinCommandElab___closed__1);
l_Lean_declareBuiltinCommandElab___closed__2 = _init_l_Lean_declareBuiltinCommandElab___closed__2();
lean::mark_persistent(l_Lean_declareBuiltinCommandElab___closed__2);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5);
l_Lean_registerBuiltinTermElabAttr___closed__1 = _init_l_Lean_registerBuiltinTermElabAttr___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__1);
l_Lean_registerBuiltinTermElabAttr___closed__2 = _init_l_Lean_registerBuiltinTermElabAttr___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__2);
l_Lean_registerBuiltinTermElabAttr___closed__3 = _init_l_Lean_registerBuiltinTermElabAttr___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__3);
l_Lean_registerBuiltinTermElabAttr___closed__4 = _init_l_Lean_registerBuiltinTermElabAttr___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__4);
l_Lean_registerBuiltinTermElabAttr___closed__5 = _init_l_Lean_registerBuiltinTermElabAttr___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__5);
l_Lean_registerBuiltinTermElabAttr___closed__6 = _init_l_Lean_registerBuiltinTermElabAttr___closed__6();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__6);
l_Lean_registerBuiltinTermElabAttr___closed__7 = _init_l_Lean_registerBuiltinTermElabAttr___closed__7();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__7);
w = l_Lean_registerBuiltinTermElabAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1 = _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__1);
l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2 = _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__2);
l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3 = _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__3);
l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4 = _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__4);
l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5 = _init_l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___lambda__1___closed__5);
l_Lean_registerBuiltinCommandElabAttr___closed__1 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__1);
l_Lean_registerBuiltinCommandElabAttr___closed__2 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__2);
l_Lean_registerBuiltinCommandElabAttr___closed__3 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__3);
l_Lean_registerBuiltinCommandElabAttr___closed__4 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__4);
l_Lean_registerBuiltinCommandElabAttr___closed__5 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__5);
l_Lean_registerBuiltinCommandElabAttr___closed__6 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__6();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__6);
l_Lean_registerBuiltinCommandElabAttr___closed__7 = _init_l_Lean_registerBuiltinCommandElabAttr___closed__7();
lean::mark_persistent(l_Lean_registerBuiltinCommandElabAttr___closed__7);
w = l_Lean_registerBuiltinCommandElabAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_mkElabAttribute___rarg___lambda__2___closed__1 = _init_l_Lean_mkElabAttribute___rarg___lambda__2___closed__1();
lean::mark_persistent(l_Lean_mkElabAttribute___rarg___lambda__2___closed__1);
l_Lean_mkElabAttribute___rarg___closed__1 = _init_l_Lean_mkElabAttribute___rarg___closed__1();
lean::mark_persistent(l_Lean_mkElabAttribute___rarg___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2();
lean::mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkTermElabAttribute___spec__4___closed__2);
l_Lean_mkTermElabAttribute___closed__1 = _init_l_Lean_mkTermElabAttribute___closed__1();
lean::mark_persistent(l_Lean_mkTermElabAttribute___closed__1);
l_Lean_mkTermElabAttribute___closed__2 = _init_l_Lean_mkTermElabAttribute___closed__2();
lean::mark_persistent(l_Lean_mkTermElabAttribute___closed__2);
l_Lean_termElabAttribute___closed__1 = _init_l_Lean_termElabAttribute___closed__1();
lean::mark_persistent(l_Lean_termElabAttribute___closed__1);
l_Lean_termElabAttribute___closed__2 = _init_l_Lean_termElabAttribute___closed__2();
lean::mark_persistent(l_Lean_termElabAttribute___closed__2);
l_Lean_termElabAttribute___closed__3 = _init_l_Lean_termElabAttribute___closed__3();
lean::mark_persistent(l_Lean_termElabAttribute___closed__3);
w = l_Lean_mkTermElabAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_termElabAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_termElabAttribute);
l_Lean_mkCommandElabAttribute___closed__1 = _init_l_Lean_mkCommandElabAttribute___closed__1();
lean::mark_persistent(l_Lean_mkCommandElabAttribute___closed__1);
l_Lean_mkCommandElabAttribute___closed__2 = _init_l_Lean_mkCommandElabAttribute___closed__2();
lean::mark_persistent(l_Lean_mkCommandElabAttribute___closed__2);
w = l_Lean_mkCommandElabAttribute(w);
if (io_result_is_error(w)) return w;
l_Lean_commandElabAttribute = io_result_get_value(w);
lean::mark_persistent(l_Lean_commandElabAttribute);
l_Lean_logUnknownDecl___closed__1 = _init_l_Lean_logUnknownDecl___closed__1();
lean::mark_persistent(l_Lean_logUnknownDecl___closed__1);
l_Lean_elabTerm___closed__1 = _init_l_Lean_elabTerm___closed__1();
lean::mark_persistent(l_Lean_elabTerm___closed__1);
l_Lean_elabTerm___closed__2 = _init_l_Lean_elabTerm___closed__2();
lean::mark_persistent(l_Lean_elabTerm___closed__2);
l_Lean_elabTerm___closed__3 = _init_l_Lean_elabTerm___closed__3();
lean::mark_persistent(l_Lean_elabTerm___closed__3);
l_Lean_elabCommand___closed__1 = _init_l_Lean_elabCommand___closed__1();
lean::mark_persistent(l_Lean_elabCommand___closed__1);
l_Lean_elabCommand___closed__2 = _init_l_Lean_elabCommand___closed__2();
lean::mark_persistent(l_Lean_elabCommand___closed__2);
l_Lean_elabCommand___closed__3 = _init_l_Lean_elabCommand___closed__3();
lean::mark_persistent(l_Lean_elabCommand___closed__3);
l_Lean_absolutizeModuleName___closed__1 = _init_l_Lean_absolutizeModuleName___closed__1();
lean::mark_persistent(l_Lean_absolutizeModuleName___closed__1);
l_Lean_processHeaderAux___closed__1 = _init_l_Lean_processHeaderAux___closed__1();
lean::mark_persistent(l_Lean_processHeaderAux___closed__1);
l_Lean_processHeaderAux___closed__2 = _init_l_Lean_processHeaderAux___closed__2();
lean::mark_persistent(l_Lean_processHeaderAux___closed__2);
l_Lean_testFrontend___closed__1 = _init_l_Lean_testFrontend___closed__1();
lean::mark_persistent(l_Lean_testFrontend___closed__1);
l_Lean_testFrontend___closed__2 = _init_l_Lean_testFrontend___closed__2();
lean::mark_persistent(l_Lean_testFrontend___closed__2);
l_Lean_testFrontend___closed__3 = _init_l_Lean_testFrontend___closed__3();
lean::mark_persistent(l_Lean_testFrontend___closed__3);
l_Lean_testFrontend___closed__4 = _init_l_Lean_testFrontend___closed__4();
lean::mark_persistent(l_Lean_testFrontend___closed__4);
l_Lean_Elab_rootNamespace___closed__1 = _init_l_Lean_Elab_rootNamespace___closed__1();
lean::mark_persistent(l_Lean_Elab_rootNamespace___closed__1);
l_Lean_Elab_rootNamespace___closed__2 = _init_l_Lean_Elab_rootNamespace___closed__2();
lean::mark_persistent(l_Lean_Elab_rootNamespace___closed__2);
l_Lean_Elab_rootNamespace = _init_l_Lean_Elab_rootNamespace();
lean::mark_persistent(l_Lean_Elab_rootNamespace);
l_Lean_Elab_resolveNamespace___closed__1 = _init_l_Lean_Elab_resolveNamespace___closed__1();
lean::mark_persistent(l_Lean_Elab_resolveNamespace___closed__1);
return w;
}
